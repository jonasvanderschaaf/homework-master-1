module HW2 where

-- Please do not add imports - that might break CodeGrade. When you are done with all
-- questions and get warnings about unused imports then you should remove them.
import Data.Function
import Data.List
import Test.QuickCheck

-- * Question 1: Free Theorems

-- Law:  (ff . map fun) xs == (map fun . ff) xs
ff :: [a] -> [a]
ff = id

-- Law: fg = fst
fg :: (a, b) -> a
fg = fst

-- Law: fh . fh = id
fh :: Either a b -> Either b a
fh (Left x) = Right x
fh (Right x) = Left x

-- Law: fmap f xs == fmap f (fi xs)
fi :: [a] -> Maybe a
fi [] = Nothing
fi (x : _) = Just x

-- * Question 2: The Farmer

data Item = Wolf | Goat | Cabbage | Farmer deriving (Eq, Show)

data Position = L | R deriving (Eq, Show)

type State = ([Item], [Item])

start :: State
start = ([Wolf, Goat, Cabbage, Farmer], [])

type Move = (Position, Maybe Item)

move :: State -> Move -> State
move (l, r) (L, Just a) = (l ++ [Farmer, a], r \\ [Farmer, a])
move (l, r) (R, Just a) = (l \\ [Farmer, a], r ++ [Farmer, a])
move (l, r) (L, Nothing) = (Farmer : l, r \\ [Farmer])
move (l, r) (R, Nothing) = (l \\ [Farmer], Farmer : r)

availableMoves :: State -> [Move]
availableMoves (l, r)
  | Farmer `elem` l = (R, Nothing) : map ((,) R . Just) (filter (/= Farmer) l)
  | otherwise = (L, Nothing) : map ((,) L . Just) (filter (/= Farmer) r)

someoneGetsEaten :: [Item] -> Bool
someoneGetsEaten xs = notElem Farmer xs && (Wolf `elem` xs && Goat `elem` xs || Cabbage `elem` xs && Goat `elem` xs)

isBad, isSolved :: State -> Bool
isBad (l, r) = someoneGetsEaten l || someoneGetsEaten r
isSolved (l, _) = null l

solve :: [State] -> State -> [[Move]]
solve prev s
  | isSolved s = [[]]
  | otherwise =
      [ m : nexts
        | m <- availableMoves s,
          let nextState = move s m,
          nextState `notElem` prev,
          not $ isBad nextState,
          nexts <- solve (s : prev) nextState
      ]

allSolutions :: [[Move]]
allSolutions = solve [] start

firstSolution :: [Move]
firstSolution = head allSolutions

optimalSolution :: [Move]
optimalSolution = minimumBy (compare `on` length) allSolutions

-- * Question 3: Modal Logic

type World = Integer

type Universe = [World]

type Proposition = Int

type Valuation = World -> [Proposition]

type Relation = [(World, World)]

data KripkeModel = KrM Universe Valuation Relation

instance Show KripkeModel where
  show (KrM u v r) = "KrM " ++ show u ++ " " ++ vstr ++ " " ++ show r
    where
      vstr = "(fromJust . flip lookup " ++ show [(w, v w) | w <- u] ++ ")"

example1 :: KripkeModel
example1 = KrM [0, 1, 2] myVal [(0, 1), (1, 2), (2, 1)]
  where
    myVal 0 = [0]
    myVal _ = [4]

example2 :: KripkeModel
example2 = KrM [0, 1] myVal [(0, 1), (1, 1)]
  where
    myVal 0 = [0]
    myVal _ = [4]

data ModForm
  = P Proposition
  | Not ModForm
  | Con ModForm ModForm
  | Box ModForm
  | Dia ModForm
  deriving (Eq, Ord, Show)

(!) :: Relation -> World -> [World]
(!) r w = map snd $ filter ((==) w . fst) r

makesTrue :: (KripkeModel, World) -> ModForm -> Bool
makesTrue (KrM _ v _, w) (P k) = k `elem` v w
makesTrue (m, w) (Not f) = not (makesTrue (m, w) f)
makesTrue (m, w) (Con f g) = makesTrue (m, w) f && makesTrue (m, w) g
makesTrue (KrM u v r, w) (Box f) = all (\w' -> makesTrue (KrM u v r, w') f) (r ! w)
makesTrue (KrM u v r, w) (Dia f) = any (\w' -> makesTrue (KrM u v r, w') f) (r ! w)

tex :: ModForm -> String
tex (P n) = "(P " ++ show n ++ ")"
tex (Not f) = "(\\lnot " ++ tex f ++ ")"
tex (Con f g) = "(" ++ tex f ++ "\\land" ++ tex g ++ ")"
tex (Box f) = "(\\Box " ++ tex f ++ ")"
tex (Dia f) = "(\\Diamond " ++ tex f ++ ")"

trueEverywhere :: KripkeModel -> ModForm -> Bool
trueEverywhere m@(KrM u _ _) f = all (curry (`makesTrue` f) m) u

strictIso :: KripkeModel -> KripkeModel -> Bool
strictIso (KrM u v r) (KrM u' v' r') =
  length u == length u'
    && all
      ( \(x, y) ->
          v x == v' y
            && all (uncurry isPair) (zip (r ! x) (r' ! y))
            && length (r ! x) == length (r' ! y)
      )
      zipped
  where
    zipped = zip u u'
    isPair x y = map snd (filter ((== x) . fst) zipped) == [y]

instance Eq KripkeModel where
  (==) (KrM u v r) (KrM u' v' r') =
    sort u == sort u'
      && all (\x -> v x == v' x) u
      && sort r == sort r'

type Bisimulation = [(World, World)]

exampleBisim :: Bisimulation
exampleBisim = [(0, 0), (1, 1), (2, 1)]

swap :: (a, b) -> (b, a)
swap (x, y) = (y, x)

checkBisim :: KripkeModel -> KripkeModel -> Bisimulation -> Bool
checkBisim (KrM _ v r) (KrM _ v' r') bisim =
  all
    ( \(x, y) ->
        v x == v' y
          && all (any (`elem` (r' ! y)) . (bisim !)) (r ! x)
          && all (any (`elem` (r ! x)) . (map swap bisim !)) (r' ! y)
    )
    bisim

type EquiRel = [[World]]

data KripkeModelS5 = KrMS5 Universe Valuation EquiRel

instance Show KripkeModelS5 where
  show (KrMS5 u v r) = "KrMS5 " ++ show u ++ " " ++ vstr ++ " " ++ show r
    where
      vstr = "(fromJust . flip lookup " ++ show [(w, v w) | w <- u] ++ ")"

example3 :: KripkeModelS5
example3 = KrMS5 [0, 1, 2] myVal [[0], [1, 2]]
  where
    myVal 0 = [3]
    myVal 1 = [2]
    myVal _ = []

makesTrueS5 :: (KripkeModelS5, World) -> ModForm -> Bool
makesTrueS5 (KrMS5 _ v _, w) (P n) = n `elem` v w
makesTrueS5 x (Con f g) = makesTrueS5 x f && makesTrueS5 x g
makesTrueS5 x (Not f) = not $ makesTrueS5 x f
makesTrueS5 (m@(KrMS5 u _ r), w) (Box f) = w `elem` u && all (\x -> makesTrueS5 (m, x) f) ws
  where
    ws = head $ filter (elem w) r
makesTrueS5 (m@(KrMS5 u _ r), w) (Dia f) = w `elem` u && any (\x -> makesTrueS5 (m, x) f) ws
  where
    ws = head $ filter (elem w) r

trueEverywhereS5 :: KripkeModelS5 -> ModForm -> Bool
trueEverywhereS5 m@(KrMS5 u _ _) f = all (\x -> makesTrueS5 (m, x) f) u

class Semantics a where
  (|=) :: (a, World) -> ModForm -> Bool

instance Semantics KripkeModel where
  (|=) = makesTrue

instance Semantics KripkeModelS5 where
  (|=) = makesTrueS5

instance Arbitrary ModForm where
  arbitrary = sized randomForm
    where
      randomForm 0 = P <$> arbitrary
      randomForm n =
        oneof
          [ P <$> arbitrary,
            Not <$> randomForm (n - 1),
            Con <$> randomForm (n `div` 2) <*> randomForm (n `div` 2),
            Box <$> randomForm (n - 1),
            Dia <$> randomForm (n - 1)
          ]

instance Arbitrary KripkeModel where
  arbitrary = do
    u <- fmap (nub . (0 :)) arbitrary
    v <- fmap (nub .) arbitrary
    r <- sublistOf [(x, y) | x <- u, y <- u]
    return $ KrM u v r

instance Arbitrary KripkeModelS5 where
  arbitrary = do
    u <- fmap (nub . (0 :)) arbitrary
    v <- fmap (nub .) arbitrary
    KrMS5 u v <$> part u
    where
      part [] = return []
      part xs = do
        ys <- sublistOf xs
        let rest = xs \\ ys
        if null ys
          then part xs
          else fmap (ys :) (part rest)

{-

Find examples by making quickcheck verify the negation of the thing we want an
example for.

Using QuickCheck to find examples:

(i) a model that satisfies p1 ^ ~[]p2:

satisfiesForm :: KripkeModel -> Bool satisfiesForm = not (flip trueEverywhere (P
1 `Con` Not (Box $ P 2)))

> quickCheck satisfiesForm

(ii) a formula that is globally true in example1 but not globally true in
example2:

exampleForm :: ModForm -> Bool exampleForm f = not (trueEverywhere example1 f &&
not (trueEverywhere example2 f))

> quickCheck exampleForm

(iii) a formula that is true at 1 in example1 but not true at 1 in example3:

exampleForm2 :: ModForm -> Bool exampleForm2 f = not (trueEverywhere example1 f
&& not ((example3,1) |= f))

> quickCheck exampleForm2

-}

tests :: [Bool]
tests =
  [ makesTrueS5 (example3, 0) (Con (Box (P 3)) (Box (Not (P 2)))),
    (example1, 1)
      |= Not
        (Box (Dia (Not (P 4)))),
    trueEverywhereS5
      example3
      ( Dia (Dia $ P 0)
          `impl` Dia (P 0)
      ),
    trueEverywhereS5 example3 (Box (P 0) `impl` P 0),
    (example3, 2) |= (Not (Box $ P 2) `Con` Not (Box $ Not $ P 2)),
    (example3, 2) |= (P 0 `disj` Not (P 0)),
    (example3, 2) |= (Box (P 0) `disj` Dia (Not (P 0)))
  ]
  where
    disj f g = Not (Not f `Con` Not g)
    impl = disj . Not
