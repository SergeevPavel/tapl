import Data.List
import Control.Applicative

type Symb = String
infixl 2 :@:
infixr 3 :->

data Type = Boo
          | Type :-> Type
          | TRcd [(Symb, Type)]
    deriving (Read,Show,Eq)

data Pat = PVar Symb
         | PRcd [(Symb, Pat)]
    deriving (Read,Show,Eq)

data Term = Fls
          | Tru
          | If Term Term Term
          | Idx Int
          | Term :@: Term
          | Lmb Symb Type Term
          | Let Pat Term Term
          | Rcd [(Symb,Term)]
          | Prj Symb Term
          deriving (Read,Show)

instance Eq Term where
  Fls       == Fls          =  True
  Tru       == Tru          =  True
  If b u w  == If b1 u1 w1  =  b == b1 && u == u1 && w == w1
  Idx m     == Idx m1       =  m == m1
  (u:@:w)   == (u1:@:w1)    =  u == u1 && w == w1
  Lmb _ t u == Lmb _ t1 u1  =  t == t1 && u == u1
  Let p u w == Let p1 u1 w1 =  p == p1 && u == u1 && w == w1
  Rcd xs    == Rcd xs1      =  xs == xs1
  Prj l u   == Prj l1 u1    =  l == l1 && u == u1
  _         == _            =  False

newtype Env = Env [(Symb,Type)]
  deriving (Read,Show,Eq)

countBinds :: Pat -> Int
countBinds (PVar _) = 1
countBinds (PRcd ls) = sum $ map (countBinds . snd) ls

shift :: Int -> Term -> Term
shift val term = go 0 term
  where
    go :: Int -> Term -> Term
    go depth (If t1 t2 t3) = If (go depth t1) (go depth t2) (go depth t3)
    go depth Fls = Fls
    go depth Tru = Tru
    go depth (Idx i) = if i < depth then Idx i else Idx $ i + val
    go depth (t1 :@: t2) = (go depth t1) :@: (go depth t2)
    go depth (Lmb s ty t) = Lmb s ty $ go (succ depth) t
    go depth (Let p ta tv) = Let p (go depth ta) (go (depth + (countBinds p)) tv)


substDB :: Int -> Term -> Term -> Term
substDB j s t = go 0 t
  where
    go :: Int -> Term -> Term
    go depth (If t1 t2 t3) = If (go depth t1) (go depth t2) (go depth t3)
    go depth Fls = Fls
    go depth Tru = Tru
    go depth (Idx i)      = if (i - depth) == j then (shift depth s) else Idx i
    go depth (t1 :@: t2)  = go depth t1 :@: go depth t2
    go depth (Lmb s ty t') = Lmb s ty $ go (succ depth) t'
    go depth (Let p ta tv) = Let p (go depth ta) (go (depth + (countBinds p)) tv)


isValue :: Term -> Bool
isValue Fls          = True
isValue Tru          = True
isValue (Lmb _ _ _)  = True
isValue t            = False


betaRuleDB :: Term -> Term
betaRuleDB (t@(Lmb _ _ _) :@: s) = let (Lmb _ _ r) = substDB (-1) s t in shift (-1) r


match :: Pat -> Term -> Maybe [(Symb, Term)]
match (PVar s) v | isValue v     = Just $ [(s, v)]
match _ _                        = Nothing


oneStep :: Term -> Maybe Term
oneStep (Idx _) = Nothing
oneStep (If Tru t _) = Just t
oneStep (If Fls _ t) = Just t
oneStep (If t1 t2 t3) = (\t1' -> If t1' t2 t3) <$> oneStep t1
oneStep t@(f@(Lmb _ _ _) :@: a) | isValue a = Just $ betaRuleDB t
                                | otherwise = (f :@:) <$> oneStep a
oneStep (t1 :@: t2) = (:@: t2) <$> oneStep t1
oneStep t@(Let p ta tv) | isValue ta = substMult <$> Just tv <*> match p ta
                        | otherwise = (\ta' -> Let p ta' tv) <$> oneStep ta
  where
    substMult :: Term -> [(Symb, Term)] -> Term
    substMult = foldr (\(_, v) t -> shift (-1) $ substDB 0 (shift 1 v) t)
oneStep _ = Nothing


whnf :: Term -> Term
whnf u | Nothing <- oneStep u = u
       | Just u' <- oneStep u = whnf u'


-- checkPat :: Pat -> Type -> Maybe Env
-- checkPat (PVar s) ty                 = Just $ Env [(s, ty)]
-- checkPat (PPair p1 p2) (ty1 :/\ ty2) = do
--   (Env e1) <- checkPat p1 ty1
--   (Env e2) <- checkPat p2 ty2
--   return $ Env (e2 ++ e1)
-- checkPat _ _                         = Nothing


-- infer :: Env -> Term -> Maybe Type
-- infer env Tru = Just Boo
-- infer env Fls = Just Boo
-- infer env (If t1 t2 t3) = do
--   ty1 <- infer env t1
--   ty2 <- infer env t2
--   ty3 <- infer env t3
--   if ty1 == Boo && ty2 == ty3
--     then Just ty2
--     else Nothing
-- infer (Env e) (Idx i) = Just $ snd (e !! i)
-- infer env (t1 :@: t2) = do
--   ty1 <- infer env t1
--   ty2 <- infer env t2
--   case ty1 of (tya :-> tyv) -> if (tya == ty2)
--                                then Just tyv
--                                else Nothing
--               otherwise     -> Nothing
-- infer (Env e) (Lmb sy tya t) = do
--   tyv <- infer (Env $ (sy, tya):e) t
--   Just $ tya :-> tyv
-- infer env@(Env e) (Let p ta tv) = do
--   tya <- infer env ta
--   (Env e') <- checkPat p tya
--   infer (Env $ e' ++ e) tv
-- infer env (Pair t1 t2) = (:/\) <$> (infer env t1) <*> (infer env t2)
-- infer env (Fst p) | Just (ty1 :/\ ty2) <- infer env p = Just ty1
-- infer env (Snd p) | Just (ty1 :/\ ty2) <- infer env p = Just ty2
-- infer env Zero = Just Nat
-- infer env (Succ t) | (Just Nat) <- infer env t = Just Nat
-- infer env (Pred t) | (Just Nat) <- infer env t = Just Nat
-- infer env (IsZero t) | (Just Nat) <- infer env t = Just Boo
-- infer env (Fix t) | (Just (ty1 :-> ty2)) <- infer env t = if ty1 == ty2 then Just ty1 else Nothing
-- infer env _ = Nothing


-- infer0 :: Term -> Maybe Type
-- infer0 = infer $ Env []
