module MuKanren where 

import Control.Monad (foldM)
import Data.List (intercalate, nub)
import Debug.Trace (trace) 
import Text.Printf (printf)

type Var = Int 

data Term = Var Var | Ctor String [Term]
          deriving (Eq)

instance Show Term where 
  show = show' where 
    show' (Var v) = "v." ++ show v 
    show' (Ctor "nil" []) = "[]"
    show' (Ctor "cons" [x, xs]) = showList (go x xs)
      where go x (Ctor "nil" []) = [x]
            go x (Ctor "cons" [y, ys]) = x : go y ys
            go x (Var v) = [x, Var v]
            go x t = [x, t]
    show' (Ctor "ReifiedVar" [Var i]) = "_." ++ show i 
    show' (Ctor name args) | name == "triple" || name == "pair"   = showTuple args
    show' (Ctor name []) = name
    show' (Ctor name args) = name ++ " " ++ showList args
    showList xs = "[" ++ showSequence xs ++ "]"
    showSequence = intercalate ", " . map show 
    showTuple args = "(" ++  showSequence args ++ ")"

type Subst = [(Var, Term)] 

type State = (Subst, Var)

type Program = State -> Stream State 

data Stream a = Nil 
              | Mature a (Stream a)
              | Immature (Stream a)

unify :: Subst -> Term -> Term -> Maybe Subst 
unify s u v = 
  go (walk s u) (walk s v) where 
    go :: Term -> Term -> Maybe Subst 
    go (Var x) (Var y) | x == y = Just s 
    go (Var x) v = occursCheck x v $ Just $ extS x v s 
    go u (Var y) = occursCheck y u $ Just $ extS y u s 
    go (Ctor n1 args1) (Ctor n2 args2) | n1 == n2 && length args1 == length args2 = 
      foldM (\subst (u, v) -> unify subst u v) s (zip args1 args2)
    go _ _ = Nothing

    occursCheck :: Var -> Term -> Maybe Subst -> Maybe Subst 
    occursCheck v term subst = 
      if v `elem` fv term then Nothing else subst 

    fv :: Term -> [Var]
    fv t = nub $ go t where 
      go (Var x) = [x] 
      go (Ctor _ ts) = concatMap fv ts 

extS :: Var -> Term -> Subst -> Subst 
extS v t s = (v, t) : s 

walk :: Subst -> Term -> Term 
walk s (Var v) = 
  case lookup v s of 
    Nothing -> Var v 
    Just x  -> walk s x
walk s u = u 

infix 4 ===
(===) :: Term -> Term -> Program 
u === v = \(s, c) -> 
  case unify s u v of 
    Just s' -> Mature (s', c) Nil
    Nothing -> Nil 

infixr 2 ||| 
(|||) :: Program -> Program -> Program 
g ||| h = \state -> mplus (g state) (h state)
 
infixr 3 &&&
(&&&) :: Program -> Program -> Program 
g &&& h = \state -> g state `bind` h 

fresh :: (Term -> Program) -> Program 
fresh f = \(s, c) -> f (Var c) (s, c + 1)

-- (|||) disjunction 
mplus :: Stream a -> Stream a -> Stream a 
mplus Nil x = x 
mplus (Mature x xs) ys = Mature x (ys `mplus` xs)
mplus (Immature xs) ys = Immature (xs `mplus` ys)

-- (&&&) conjunction 
bind :: Stream a -> (a -> Stream b) -> Stream b
Nil `bind` _ = Nil 
Mature x xs `bind` f = f x `mplus` (xs `bind` f) 
Immature xs `bind` f = Immature (xs `bind` f)

streamToList Nil = [] 
streamToList (Mature x xs) = x : streamToList xs 
streamToList (Immature xs) = streamToList xs 

emptyState = ([], 0)

atom name = Ctor name []

zzz g state = Immature (g state) 

five = fresh (\x -> (===) x (atom "5"))
fives_ x = (|||) ((===) x (atom "5")) (zzz $ fives_ x)
fives = fresh fives_

fivesRev_ x = (|||) (zzz $ fivesRev_ x) ((===) x (atom "5"))
fivesRev = fresh fivesRev_

a_and_b = (&&&)
          (fresh (\a -> (===) a (atom "7")))
          (fresh (\b -> (|||) ((===) b (atom "5")) ((===) b (atom "6"))))

runTest :: Int -> Program -> [Term]
-- runTest :: Int -> Program -> [State]
runTest n p = 
  let select = if n > 0 then take n else id in
  -- map reifyFst $ 
  let selected = select $ streamToList (p emptyState) in 
  map reifyFst selected

nil = atom "nil"
cons x xs = Ctor "cons" [x, xs]

intList xs = foldr (\x lst -> cons (atom $ show x) lst) nil xs 

appendo xs ys zs = 
  (xs === nil &&& zs === ys)
  ||| (fresh $ \h -> fresh $ \t -> fresh $ \r -> 
         xs === cons h t &&& 
         zzz (appendo t ys r) &&&
         zs === cons h r 
      )

deepWalk :: Subst -> Term -> Term
deepWalk s t = 
  case walk s t of
    Ctor name args | name /= "ReifiedVar" -> Ctor name (map (deepWalk s) args)
    t' -> t'

reifyS :: Term -> Subst -> Subst
reifyS t s = 
  -- let res = 
        case walk s t of
          Var v -> let n = Ctor "ReifiedVar" [Var (length s)] in (v, n) : s
          Ctor name args | name /= "ReifiedVar" -> foldl (\subst u -> reifyS u subst) s args
          _ -> s 
  -- in  trace (printf "\nIn reifyS\nt: %s\ns: %s\nres: %s\n" (show t) (show s) (show res)) $ res 

reifyFst :: State -> Term
reifyFst sc = 
  let v = deepWalk (fst sc) (Var 0) in 
  deepWalk (reifyS v []) v

test0 = 
  runTest (-1) (fresh $ \zs -> 
    appendo (intList [1,2,3]) 
      (Ctor "cons" [Ctor "abc" [], Ctor "nil" []]) zs)

test01 = 
  runTest (-1) (fresh $ \zs -> 
    appendo (intList ([] :: [Int])) (intList [4,5]) zs)

test1 = 
  runTest 3 ( fresh $ \q -> 
              fresh $ \xs -> 
              fresh $ \ys -> 
              fresh $ \zs -> 
                q === Ctor "triple" [xs, ys, zs] &&& 
                zzz (appendo xs ys zs))

test11 = 
  runTest 3 ( fresh $ \q -> 
              fresh $ \ys -> 
              fresh $ \zs -> 
                q === Ctor "pair" [ys, zs] &&& 
                 zzz (appendo (intList [1,2,3,4]) ys zs))

test2 = 
  runTest 6 ( fresh $ \q -> 
              fresh $ \xs -> 
              fresh $ \zs -> 
                q === Ctor "pair" [xs, zs] &&& zzz (appendo xs nil zs))

run x = putStrLn $ unlines $ map show x
