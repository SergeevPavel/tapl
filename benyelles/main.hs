import Data.List

type Symb = String

infixr 3 :->

data Type = TVar Symb      -- типовой атом
          | Type :-> Type  -- стрелочный тип
    deriving (Read,Show,Eq,Ord)

type Ctx = [Type] -- контекст

data TNF = Meta   -- метапеременная (пока еще бесструктурная часть схемы)
             Type   -- типизированна
         | TNF    -- структурированная часть схемы
             Ctx    -- абстрактор
             Int    -- головная переменная как индекс Де Брауна
             [TNF]  -- бёмовы хвостики
    deriving (Read,Show,Eq,Ord)

uncurry2List  :: Type -> (Symb,[Type])
uncurry2List (TVar s) = (s, [])
uncurry2List (ty1 :-> ty2) = fmap (ty1 :) $ uncurry2RevList ty2

uncurry2RevList :: Type -> (Symb,[Type])
uncurry2RevList ty = go [] ty
  where
    go :: [Type] -> Type -> (Symb, [Type])
    go args (TVar s) = (s, args)
    go args (ty1 :-> ty2) = go (ty1 : args) ty2


combine :: [[a]] -> [[a]]
combine []     = [[]]
combine [x]    = fmap (:[]) x
combine (x:xs) = (:) <$> x <*> combine xs


unMeta :: Ctx -> TNF -> [TNF]
unMeta ctx (Meta ty) = let (sym, args) = uncurry2RevList ty
                           candidates = filter (\((s,_), i) -> s == sym) $ zip (uncurry2List <$> args ++ ctx) [0..]
                       in fmap (\((s, tls), i) -> TNF args i (map Meta tls)) candidates
unMeta ctx (TNF abs hv tls) = TNF abs hv <$> (combine (fmap (unMeta (abs ++ ctx)) tls))


isTerm :: TNF -> Bool
isTerm (TNF _ _ tls) | and $ isTerm <$> tls = True
isTerm _                                    = False

allTNFGens :: Type -> [[TNF]]
allTNFGens tau = (takeWhile (/= [])) $ iterate ((concatMap (unMeta [])) . (filter (not . isTerm))) [Meta tau]

inhabGens :: Type -> [[TNF]]
inhabGens tau = (filter isTerm) <$> allTNFGens tau

inhabs :: Type -> [TNF]
inhabs = concat . inhabGens


tArr = TVar "a" :-> TVar "a"

tNat = tArr :-> tArr

tBool = TVar "a" :-> TVar "a" :-> TVar "a"

tK = TVar "a" :-> TVar "b" :-> TVar "a"

tKast = TVar "a" :-> TVar "b" :-> TVar "b"

tBiNat = (TVar "a" :-> TVar "a") :-> (TVar "a" :-> TVar "a") :-> TVar "a" :-> TVar "a"

tBiBiNat = (TVar "a" :-> TVar "b") :-> (TVar "b" :-> TVar "a") :-> TVar "a" :-> TVar "a"

tBinTree = (TVar "a" :-> TVar "a" :-> TVar "a") :-> TVar "a" :-> TVar "a"

hw3last1 = ((TVar "a" :-> TVar "b") :-> TVar "a") :-> (TVar "a" :-> TVar "a" :-> TVar "b") :-> TVar "a"

hw3last2 = ((TVar "a" :-> TVar "b") :-> TVar "a") :-> (TVar "a" :-> TVar "a" :-> TVar "b") :-> TVar "b"

t3 = ((TVar "a" :-> TVar "a") :-> TVar "a") :-> TVar "a"

contFmapT = (TVar "a" :-> TVar "b") :->  ((TVar "a" :-> TVar "c") :-> TVar "d")
               :-> (TVar "b" :-> TVar "c") :-> TVar "d"

selFmapT = (TVar "a" :-> TVar "b") :->  ((TVar "a" :-> TVar "c") :-> TVar "a")
               :-> (TVar "b" :-> TVar "c") :-> TVar "b"

monsterT = (((TVar "a" :-> TVar "a") :-> TVar "a") :-> TVar "a") :-> TVar "a" :-> TVar "a"

fixT = (TVar "a" :-> TVar "a") :-> TVar "a"

peirceT = ((TVar "p" :-> TVar "q") :-> TVar "p") :-> TVar "p"
