module Main where

-- minamoto-kanren

data Term = Var String | Value String | Functor String [Term] deriving (Eq, Show)
type Subst = [(String, Term)]
type State = (Subst, Integer)
type Goal = State -> [State]

falsify :: Goal
falsify _ = []

succeed :: Goal
succeed x = [x]

disj :: Goal -> Goal -> Goal
disj x y = \s -> (x s) ++ (y s)

conj :: Goal -> Goal -> Goal
conj x y =
  \s -> case map y (x s) of
    [] -> []
    t -> foldl1 (++) t

emptySubst :: Subst
emptySubst = []

emptyState :: State
emptyState = (emptySubst, 0)

extendSubst :: (String, Term) -> Subst -> Subst
extendSubst (k, v) s = (k, v):s

lookupSubst :: Term -> Subst -> Maybe Term
lookupSubst t s =
  case t of
    Value _ -> Just t
    Functor _ _ -> Just t
    Var k ->
      case s of
        [] -> Nothing
        (kk,vv):res -> if k == kk then Just vv else lookupSubst t res

fresh :: State -> (Term, State)
fresh (s, k) = (Var ("V_" ++ show k), (s, k + 1))

unify :: Term -> Term -> Subst -> Maybe Subst
unify t1 t2 s = if t1Res == t2Res then Just s else unify' t1Res t2Res s
  where
    t1Res = ofs t1 $ lookupSubst t1 s
    t2Res = ofs t2 $ lookupSubst t2 s
    ofs t Nothing = t
    ofs _ (Just t) = t

unify' :: Term -> Term -> Subst -> Maybe Subst
unify' (Value v) (Value v2) s = if v == v2 then Just s else Nothing
unify' (Var k) v s = Just $ extendSubst (k, v) s
unify' v (Var k) s = Just $ extendSubst (k, v) s
unify' (Functor f1 arglst1) (Functor f2 arglst2) s =
  if f1 /= f2 then Nothing
  else if length arglst1 /= length arglst2 then Nothing
  else unify'' arglst1 arglst2 s

unify'' :: [Term] -> [Term] -> Subst -> Maybe Subst
unify'' [] [] s = Just s
unify'' [] _ s = Nothing
unify'' _ [] s = Nothing
unify'' (a:as) (b:bs) s =
  case unify a b s of
    Nothing -> Nothing
    Just newS -> unify'' as bs newS
  
vx = Var "X"
vy = Var "Y"
vz = Var "Z"
vq = Var "Q"

infixl ===
(===) :: Term -> Term -> Goal
(===) t1 t2 =
  \(s, k) ->
    case unify t1 t2 s of
      Nothing -> falsify (s, k)
      Just ss -> succeed (ss, k)
  
run :: Goal -> [State]
run g = g emptyState

choice :: Term -> [Term] -> Goal
choice v [] = falsify
choice v (s:ss) = disj (v === s) (choice v ss)

commonEl :: [Term] -> [Term] -> Goal
commonEl l1 l2 = conj (choice vx l1) (choice vx l2)

conso a b l = Functor "cons" [a, b] === l

-- we simulate list w/ first-order embedded functors.

fCons :: Term -> Term -> Term
fCons a b = Functor "cons" [a, b]

fNil :: Term
fNil = Functor "nil" []

fList :: [Term] -> Term
fList [] = Functor "nil" []
fList (x:xs) = Functor "cons" [x, fList xs]

-- the reason why eta-expansion is needed in sokuza kanren
-- is because scheme is call-by-value. this is not needed
-- in haskell because haskell is lazy.
-- the same goes for conjN, which is defined as a macro w/
-- eta-expansion in sokuza kanren but has the same definition
-- as disjN here.
appendo :: Term -> Term -> Term -> Goal
appendo l1 l2 l3 =
  disj
    -- append([], X, X)
    (conj (l1 === fNil) (l2 === l3))
    -- append(L1, L2, L3)
    (\s ->
       -- NOTE: we cannot do `let (h, s) = fresh s` here because haskell.
       let (h, s1) = fresh s
       in let (t, s2) = fresh s1
       in let (l3p, s3) = fresh s2
       in
         conjN [
             conso h t l1  -- [H|T] = L1
           , conso h l3p l3  -- [H|L3P] = L3
           , appendo t l2 l3p -- append(T, L2, L3P)
         ]
         s3
    )

conjN :: [Goal] -> Goal
conjN [] = succeed
conjN [x] = x
conjN (x:xs) = conj x (conjN xs)

disjN :: [Goal] -> Goal
disjN [] = falsify
disjN [x] = x
disjN (x:xs) = disj x (disjN xs)

lookupN :: Term -> Subst -> Term
lookupN t s =
  case lookupSubst t s of
    Nothing -> t
    Just k ->
      case k of
        Var _ -> k
        Value _ -> k
        Functor f args -> Functor f (map (\t -> lookupN t s) args)

runFull :: Goal -> [Term]
runFull g = map (\(s, _)-> lookupN vq s) (g emptyState)

fListOf :: [String] -> Term
fListOf s = fList $ map Value s

main :: IO ()
main = do
  putStrLn $ show $ runFull $ appendo (fListOf ["1", "2"]) (fListOf ["3"]) vq
  putStrLn $ show $ runFull $ appendo vq (fListOf ["4", "5"]) (fListOf ["1", "2", "3", "4", "5"])
  putStrLn $ show $ runFull $ appendo vq vx (fListOf ["1", "2", "3", "4", "5"])
  putStrLn $ show $ runFull $ appendo vx vq (fListOf ["1", "2", "3", "4", "5"])
  putStrLn $ show $ runFull $ (
    \s -> let (x, s1) = fresh s
          in let (y, s2) = fresh s1
             in
               conjN [
               appendo x y (fListOf ["1", "2", "3", "4", "5"])
               , (Functor "pair" [x, y] === vq)
               ] s2
               
    )
      
  
