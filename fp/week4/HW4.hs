module HW4 where

import Data.List
import Data.Maybe

-- * Question 1: PAL

(!) :: (Eq a) => [(a, b)] -> a -> b
(!) v x = fromJust (lookup x v)

(?) :: (Eq a) => [[a]] -> a -> [a]
(?) lls x = head (filter (x `elem`) lls)

type Prop = Int

type Agent = String

data Form = Top | P Prop | Neg Form | Con Form Form | K Agent Form | Ann Form Form
  deriving (Eq, Ord, Show)

type World = Int

type Relations = [(Agent, [[World]])]

type Valuation = [(World, [Prop])]

data Model = Mo
  { worlds :: [World],
    rel :: Relations,
    val :: Valuation
  }
  deriving (Eq, Ord, Show)

isTrue :: (Model, World) -> Form -> Bool
isTrue _ Top = True
isTrue (m, w) (P p) = p `elem` (val m ! w)
isTrue (m, w) (Neg f) = not (isTrue (m, w) f)
isTrue (m, w) (Con f g) = isTrue (m, w) f && isTrue (m, w) g
isTrue (m, w) (K i f) = and [isTrue (m, w') f | w' <- (rel m ! i) ? w]
isTrue (m, w) (Ann f g) = isTrue (m, w) f <= isTrue (announce m f, w) g

(|=) :: (Model, World) -> Form -> Bool
(|=) = isTrue

announce :: Model -> Form -> Model
announce oldModel f = Mo newWorlds newRel newVal
  where
    newWorlds = filter (\x -> (oldModel, x) |= f) $ worlds oldModel
    newRel = fmap (fmap (filter (`elem` newWorlds))) <$> rel oldModel
    newVal = filter (\(x, _) -> x `elem` newWorlds) $ val oldModel

kw :: Agent -> Form -> Form
kw i f = dis (K i f) (K i (Neg f))

muddyStart :: Model
muddyStart =
  Mo
    [0, 1, 2, 3, 4, 5, 6, 7]
    [ ("1", [[0, 4], [2, 6], [3, 7], [1, 5]]),
      ("2", [[0, 2], [4, 6], [5, 7], [1, 3]]),
      ("3", [[0, 1], [4, 5], [6, 7], [2, 3]])
    ]
    [ (0, []),
      (1, [3]),
      (2, [2]),
      (3, [2, 3]),
      (4, [1]),
      (5, [1, 3]),
      (6, [1, 2]),
      (7, [1, 2, 3])
    ]

dis :: Form -> Form -> Form
dis f g = Neg (Con (Neg f) (Neg g))

atLeastOne :: Form
atLeastOne = dis (P 1) (dis (P 2) (P 3))

conSet :: [Form] -> Form
conSet = foldr Con Top

nobodyKnowsOwn :: Form
nobodyKnowsOwn = conSet [Neg $ kw (show i) (P i) | i <- [1 :: Int .. 3]]

everyoneKnowsAll :: Form
everyoneKnowsAll = conSet [kw (show i) (P i) | i <- [1 :: Int .. 3]]

-- * Question 2: NSA Puzzle: Explicit Solution

data Class = Calc1 | Calc2 | Calc3 deriving (Eq, Ord, Show, Enum)

type Time = Int

data Building = North | West | East | South deriving (Eq, Ord, Show, Enum)

type Case = (Class, Time, Building)

-- Use the following atomic propositions:
-- 1,2,3, -- Calc1, Calc2, Calc3
-- 103,109,110,111,112 -- 3, 9, 10, 11, noon
-- 201,202,203,204 -- North, East, South, West

julia, michael, mary :: Agent -- use this for "K mary ..." etc.
(julia, michael, mary) = ("julia", "michael", "mary")

solutions :: [Case]
solutions =
  map worldToCase $
    worlds $
      initialModel `announce` annOne `announce` annTwo `announce` annThree

allCases :: [Case]
allCases =
  [ (Calc1, 9, North),
    (Calc2, 12, West),
    (Calc1, 3, West),
    (Calc1, 10, East),
    (Calc2, 10, North),
    (Calc1, 10, South),
    (Calc1, 10, North),
    (Calc2, 11, East),
    (Calc3, 12, West),
    (Calc2, 12, South)
  ]

worldToCase :: World -> Case
worldToCase = (allCases !!)

caseToWorld :: Case -> World
caseToWorld c = fromJust (elemIndex c allCases)

initialModel :: Model
initialModel = Mo ws rs vs
  where
    ws = [0 .. length allCases - 1]
    rs =
      [ (julia, [(fmap caseToWorld . filter ((== c) . tripleFst)) allCases | c <- enumFrom Calc1]),
        (michael, [(fmap caseToWorld . filter ((== t) . tripleSnd)) allCases | t <- [3, 9, 10, 11, 12]]),
        (mary, [(fmap caseToWorld . filter ((== b) . tripleThrd)) allCases | b <- enumFrom North])
      ]
    vs = fmap (\w -> (w, (caseToProps . worldToCase) w)) ws

tripleFst :: (a, b, c) -> a
tripleFst (x, _, _) = x

tripleSnd :: (a, b, c) -> b
tripleSnd (_, y, _) = y

tripleThrd :: (a, b, c) -> c
tripleThrd (_, _, z) = z

classToProp :: Class -> Int
classToProp Calc1 = 1
classToProp Calc2 = 2
classToProp Calc3 = 3

buildingToProp :: Building -> Int
buildingToProp North = 201
buildingToProp East = 202
buildingToProp South = 203
buildingToProp West = 204

caseToProps :: Case -> [Prop]
caseToProps (x, y, z) = [classToProp x, 100 + y, buildingToProp z]

caseToForm :: Case -> Form
caseToForm = conSet . fmap P . caseToProps

annOne, annTwo, annThree :: Form
annOne =
  conSet
    [K michael $ Neg $ K julia $ caseToForm c | c <- allCases]
    `Con` conSet
      [K mary $ Neg $ K julia $ caseToForm c | c <- allCases]
annTwo =
  conSet
    [Neg $ K michael $ caseToForm c | c <- allCases]
    `Con` conSet
      [Neg $ K mary $ caseToForm c | c <- allCases]
annThree =
  Neg $ conSet [Neg $ K julia $ caseToForm c | c <- allCases]

-- * Question 3: NSA Puzzle: Symbolic Solution

noCodeForThisQuestion :: ()
noCodeForThisQuestion = () -- write your solution into "HW4-substitute.smcdel.txt"

{-
I found working with haskell to be easier than with smcdel because I was more
familiar with haskell beforehand and did not have to learn new syntax. I would
expect that if I used it for a longer time, I would become more comfortable with
the tools.

One small improvement I would suggest is auto-closing parentheses: noone ever
uses a single parenthesis.
-}

-- * Question 5: StateIO

newtype StateIO s a = SIO {runSIO :: s -> IO (a, s)} -- for parts (a) to (c)

newtype StateT m s a = ST {run :: s -> m (a, s)} -- for part (d)

put :: (Monad m) => s -> StateT m s ()
put s' = ST $ \_s -> return ((), s')

get :: (Monad m) => StateT m s s
get = ST $ \x -> return (x, x)

lift :: (Monad m) => m a -> StateT m s a
lift ia = ST $ \s -> do
  a <- ia
  return (a, s)

instance (Monad m) => Functor (StateT m s) where
  fmap ab (ST sa) = ST $ \s -> do
    (a, s') <- sa s
    let b = ab a
    return (b, s')

instance (Monad m) => Applicative (StateT m s) where
  pure a = ST $ \s -> return (a, s)
  (ST sab) <*> (ST sa) = ST $ \s -> do
    (ab, s') <- sab s
    (a, s'') <- sa s'
    let b = ab a
    return (b, s'')

-- Variable naming in Haskell is hard
instance (Monad m) => Monad (StateT m s) where
  (>>=) (ST f) g = ST $ \s -> do
    (x, y) <- f s
    let (ST u) = g x
    u y

-- monad m=IO, state type s=Int, value type a=()
askCount :: StateT IO Int ()
askCount = do
  lift $ putStrLn "What is your name?"
  n <- lift getLine
  lift $ putStrLn $ "Nice to meet you, " ++ n ++ "."
  k <- get
  let k' = k + length (filter (`elem` "aeiou") n)
  put k'
  lift $ putStrLn $ "I have seen " ++ show k' ++ " vowels so far."
  askCount

-- monad m=Maybe, state type s=[String], value type a=Int
safeLogDivide :: Int -> Int -> StateT Maybe [[Char]] Int
safeLogDivide _ 0 = lift Nothing
safeLogDivide x y = do
  oldLog <- get
  put $ oldLog ++ ["Divided by " ++ show y]
  return (x `div` y)
