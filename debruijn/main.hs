import Data.List
import Control.Applicative

type Symb = String
infixl 2 :@:
infixr 3 :->

data Type = Boo
          | Nat
          | Type :-> Type
          | Type :/\ Type
    deriving (Read,Show,Eq)

data Pat = PVar Symb
         | PPair Pat Pat
    deriving (Read,Show,Eq)

data Term = Fls
          | Tru
          | If Term Term Term
          | Zero
          | Succ Term
          | Pred Term
          | IsZero Term
          | Idx Int
          | Term :@: Term
          | Lmb Symb Type Term
          | Let Pat Term Term
          | Pair Term Term
          | Fst Term
          | Snd Term
          | Fix Term
          deriving (Read,Show)

instance Eq Term where
  Fls       == Fls         =  True
  Tru       == Tru         =  True
  If b u w  == If b1 u1 w1 =  b == b1 && u == u1 && w == w1
  Idx m     == Idx m1      =  m == m1
  (u:@:w)   == (u1:@:w1)   =  u == u1 && w == w1
  Lmb _ t u == Lmb _ t1 u1 =  t == t1 && u == u1
  Let p u w == Let p1 u1 w1 =  p == p1 && u == u1 && w == w1
  Pair u w  == Pair u1 w1  =  u == u1 && w == w1
  Fst p     == Fst p1      =  p == p1
  Snd p     == Snd p1      =  p == p1
  _         == _           =  False


newtype Env = Env [(Symb,Type)]
  deriving (Read,Show,Eq)

countBinds :: Pat -> Int
countBinds (PVar _) = 1
countBinds (PPair p1 p2) = countBinds p1 + countBinds p2

shift :: Int -> Term -> Term
shift val term = go 0 term
  where
    go :: Int -> Term -> Term
    go depth (If t1 t2 t3) = If (go depth t1) (go depth t2) (go depth t3)
    go depth Fls = Fls
    go depth Tru = Tru
    go depth Zero = Zero
    go depth (Succ t) = Succ (go depth t)
    go depth (Pred t) = Pred (go depth t)
    go depth (IsZero t) = IsZero (go depth t)
    go depth (Idx i) = if i < depth then Idx i else Idx $ i + val
    go depth (t1 :@: t2) = (go depth t1) :@: (go depth t2)
    go depth (Lmb s ty t) = Lmb s ty $ go (succ depth) t
    go depth (Let p ta tv) = Let p (go depth ta) (go (depth + (countBinds p)) tv)
    go depth (Pair t1 t2) = Pair (go depth t1) (go depth t2)
    go depth (Fst t) = Fst $ go depth t
    go depth (Snd t) = Snd $ go depth t
    go depth (Fix t) = Fix $ go depth t


substDB :: Int -> Term -> Term -> Term
substDB j s t = go 0 t
  where
    go :: Int -> Term -> Term
    go depth (If t1 t2 t3) = If (go depth t1) (go depth t2) (go depth t3)
    go depth Fls = Fls
    go depth Tru = Tru
    go depth Zero = Zero
    go depth (Succ t) = Succ (go depth t)
    go depth (Pred t) = Pred (go depth t)
    go depth (IsZero t) = IsZero (go depth t)
    go depth (Idx i)      = if (i - depth) == j then (shift depth s) else Idx i
    go depth (t1 :@: t2)  = go depth t1 :@: go depth t2
    go depth (Lmb s ty t') = Lmb s ty $ go (succ depth) t'
    go depth (Let p ta tv) = Let p (go depth ta) (go (depth + (countBinds p)) tv)
    go depth (Pair t1 t2)  = Pair (go depth t1) (go depth t2)
    go depth (Fst t)       = Fst $ go depth t
    go depth (Snd t)       = Snd $ go depth t
    go depth (Fix t)       = Fix $ go depth t


isNV :: Term -> Bool
isNV Zero              = True
isNV (Succ t) | isNV t = True
isNV _                 = False


isValue :: Term -> Bool
isValue Fls          = True
isValue Tru          = True
isValue (Lmb _ _ _)  = True
isValue (Pair t1 t2) = isValue t1 && isValue t2
isValue t            = isNV t


betaRuleDB :: Term -> Term
betaRuleDB (t@(Lmb _ _ _) :@: s) = let (Lmb _ _ r) = substDB (-1) s t in shift (-1) r


match :: Pat -> Term -> Maybe [(Symb, Term)]
match (PVar s) v | isValue v     = Just $ [(s, v)]
match (PPair p1 p2) (Pair t1 t2) = (++) <$> match p1 t1 <*> match p2 t2
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
oneStep (Pair t1 t2) = (Pair <$> oneStep t1 <*> Just t2) <|> (Pair <$> Just t1 <*> oneStep t2)
oneStep (Fst p) | (not (isValue p)) = Fst <$> oneStep p
                | (Pair t1 _) <- p = Just t1
oneStep (Snd p) | (not (isValue p)) = Snd <$> oneStep p
                | (Pair _ t2) <- p = Just t2
oneStep (Succ t) = Succ <$> oneStep t
oneStep (Pred Zero)              = Just Zero
oneStep (Pred (Succ t)) | isNV t = Just t
oneStep (Pred t)                 = Pred <$> oneStep t
oneStep (IsZero Zero)              = Just Tru
oneStep (IsZero (Succ t)) | isNV t = Just Fls
oneStep (IsZero t)                 = IsZero <$> oneStep t
oneStep fp@(Fix (Lmb s ty t)) = Just (shift (-1) $ substDB 0 (shift 1 fp) t)
oneStep (Fix t) = Fix <$> oneStep t
oneStep _ = Nothing


whnf :: Term -> Term
whnf u | Nothing <- oneStep u = u
       | Just u' <- oneStep u = whnf u'


checkPat :: Pat -> Type -> Maybe Env
checkPat (PVar s) ty                 = Just $ Env [(s, ty)]
checkPat (PPair p1 p2) (ty1 :/\ ty2) = do
  (Env e1) <- checkPat p1 ty1
  (Env e2) <- checkPat p2 ty2
  return $ Env (e2 ++ e1)
checkPat _ _                         = Nothing


infer :: Env -> Term -> Maybe Type
infer env Tru = Just Boo
infer env Fls = Just Boo
infer env (If t1 t2 t3) = do
  ty1 <- infer env t1
  ty2 <- infer env t2
  ty3 <- infer env t3
  if ty1 == Boo && ty2 == ty3
    then Just ty2
    else Nothing
infer (Env e) (Idx i) = Just $ snd (e !! i)
infer env (t1 :@: t2) = do
  ty1 <- infer env t1
  ty2 <- infer env t2
  case ty1 of (tya :-> tyv) -> if (tya == ty2)
                               then Just tyv
                               else Nothing
              otherwise     -> Nothing
infer (Env e) (Lmb sy tya t) = do
  tyv <- infer (Env $ (sy, tya):e) t
  Just $ tya :-> tyv
infer env@(Env e) (Let p ta tv) = do
  tya <- infer env ta
  (Env e') <- checkPat p tya
  infer (Env $ e' ++ e) tv
infer env (Pair t1 t2) = (:/\) <$> (infer env t1) <*> (infer env t2)
infer env (Fst p) | Just (ty1 :/\ ty2) <- infer env p = Just ty1
infer env (Snd p) | Just (ty1 :/\ ty2) <- infer env p = Just ty2
infer env Zero = Just Nat
infer env (Succ t) | (Just Nat) <- infer env t = Just Nat
infer env (Pred t) | (Just Nat) <- infer env t = Just Nat
infer env (IsZero t) | (Just Nat) <- infer env t = Just Boo
infer env (Fix t) | (Just (ty1 :-> ty2)) <- infer env t = if ty1 == ty2 then Just ty1 else Nothing
infer env _ = Nothing


infer0 :: Term -> Maybe Type
infer0 = infer $ Env []



one   = Succ Zero
two   = Succ one
three = Succ two
four  = Succ three
five  = Succ four
six   = Succ five
seven = Succ six
eight = Succ seven
nine  = Succ eight
ten   = Succ nine

plus_ = Lmb "f" (Nat :-> Nat :-> Nat) $ Lmb "m" Nat $ Lmb "n" Nat $
  If (IsZero $ Idx 1)
     (Idx 0)
     (Succ $ Idx 2 :@: Pred (Idx 1) :@: Idx 0)
plus = Fix plus_

minus_ = Lmb "f" (Nat :-> Nat :-> Nat) $ Lmb "m" Nat $ Lmb "n" Nat $
  If (IsZero $ Idx 0)
     (Idx 1)
     (Pred $ Idx 2 :@: Idx 1 :@: Pred (Idx 0))
minus = Fix minus_

eq_ = Lmb "f" (Nat :-> Nat :-> Boo) $ Lmb "m" Nat $ Lmb "n" Nat $
  If (IsZero $ Idx 1)
     (IsZero $ Idx 0)
     (If (IsZero $ Idx 0)
         (IsZero $ Idx 1)
         (Idx 2 :@: Pred (Idx 1) :@: Pred (Idx 0)))
eq = Fix eq_

mult_ = Lmb "f" (Nat :-> Nat :-> Nat) $ Lmb "m" Nat $ Lmb "n" Nat $
  If (IsZero $ Idx 1)
     Zero
     (plus :@: Idx 0 :@: (Idx 2 :@: Pred (Idx 1) :@: Idx 0))
mult = Fix mult_

power_  = Lmb "f" (Nat :-> Nat :-> Nat) $ Lmb "m" Nat $ Lmb "n" Nat $
  If (IsZero $ Idx 0)
     one
     (mult :@: Idx 1 :@: (Idx 2 :@: Idx 1 :@: Pred (Idx 0)))
power = Fix power_
