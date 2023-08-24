module HW1 where

import Data.List
import Data.Maybe (isNothing)

{-# ANN module "HLint: ignore Use map" #-}

-- Question 1: map, filter, zip

myMap :: (a -> b) -> [a] -> [b]
myMap _ [] = []
myMap f (x : xs) = f x : myMap f xs

myOtherMap :: (a -> b) -> [a] -> [b]
myOtherMap f xs = [f x | x <- xs]

myFilter :: (a -> Bool) -> [a] -> [a]
myFilter _ [] = []
myFilter p (x : xs)
  | p x = x : myFilter p xs
  | otherwise = myFilter p xs

myOtherFilter :: (a -> Bool) -> [a] -> [a]
myOtherFilter p xs = [x | x <- xs, p x]

myZip :: [a] -> [b] -> [(a, b)]
myZip (x : xs) (y : ys) = (x, y) : myZip xs ys
myZip _ _ = []

mystery :: (b -> c) -> (a, b) -> (a, c)
mystery = fmap

-- Question 2: Primes

divides :: Integer -> Integer -> Bool
divides n m = (m `mod` n) == 0

-- This is not particularly nice, but it will do
isPrime :: Integer -> Bool
isPrime n = not (any (`divides` n) [2 .. n - 1]) && n /= 1

-- Question 3: Luhn Algorithm

-- This was inspired by the ChatGPT example given in the lecture
luhn :: Integer -> Bool
luhn x
  | even len = sum (mapAlt (sum . digits . (* 2)) id (digits x)) `mod` 10 == 0
  | otherwise = sum (mapAlt id (sum . digits . (* 2)) (digits x)) `mod` 10 == 0
  where
    ds = digits x
    len = length ds
    mapAlt _ _ [] = []
    mapAlt f _ [y] = [f y]
    mapAlt f g (y : z : xs) = f y : g z : mapAlt f g xs

digits :: Integer -> [Integer]
digits n = map (\x -> read [x]) (show n)

isAmericanExpress, isMaster, isVisa :: Integer -> Bool
isAmericanExpress n = take 2 (digits n) == [3, 4] || take 2 (digits n) == [3, 7]
isMaster = (== 5) . head . digits
isVisa = (== 4) . head . digits

-- Question 4: Show and Eq

newtype UnOrdPair a = UOP (a, a)

instance (Show a, Ord a) => Show (UnOrdPair a) where
  show (UOP x) = "UOP " ++ "(" ++ show (uncurry min x) ++ "," ++ show (uncurry max x) ++ ")"

instance Ord a => Eq (UnOrdPair a) where
  (==) (UOP x1) (UOP x2) =
    uncurry max x1 == uncurry max x2
      && uncurry min x1 == uncurry min x2

-- Question 5: Propositional Logic

data Form = P Integer | Neg Form | Conj Form Form | Disj Form Form | Con [Form] | Dis [Form] | Top
  deriving (Eq, Ord, Show)

impl :: Form -> Form -> Form
impl a b = Neg a `Disj` b

biImpl :: Form -> Form -> Form
biImpl a b = impl a b `Conj` impl b a

type Assignment = [Integer]

satisfies :: Assignment -> Form -> Bool
satisfies v (P k) = k `elem` v
satisfies v (Neg f) = not (satisfies v f)
satisfies v (Conj f g) = satisfies v f && satisfies v g
satisfies v (Disj f g) = satisfies v f || satisfies v g
satisfies v (Con l) = all (satisfies v) l
satisfies v (Dis l) = any (satisfies v) l
satisfies _ Top = True

variablesIn :: Form -> [Integer]
variablesIn (P a) = [a]
variablesIn Top = []
variablesIn (Neg f) = variablesIn f
variablesIn (Conj f g) = nub $ variablesIn f ++ variablesIn g
variablesIn (Disj f g) = nub $ variablesIn f ++ variablesIn g
variablesIn (Con l) = nub $ l >>= variablesIn
variablesIn (Dis l) = nub $ l >>= variablesIn

allAssignmentsFor :: [Integer] -> [Assignment]
allAssignmentsFor [] = [[]]
allAssignmentsFor (x : xs) = map (x :) assigns ++ assigns
  where
    assigns = allAssignmentsFor xs

isValid :: Form -> Bool
isValid f = all (`satisfies` f) $ allAssignmentsFor $ variablesIn f

sat :: Form -> Maybe Assignment
sat f = safeHead $ filter (`satisfies` f) $ allAssignmentsFor $ variablesIn f
  where
    safeHead [] = Nothing
    safeHead (x : _) = Just x

tests :: [Bool]
tests =
  [ not . isValid $ P 1,
    isValid $ Neg (Conj (P 1) (Neg (P 1))),
    isValid $ P 1 `Disj` Neg (P 1),
    isValid $
      biImpl
        (Neg $ Neg (P 1) `Conj` Neg (P 2))
        (P 1 `Disj` P 2),
    isValid $
      Con
        [Top, Neg $ Neg Top],
    not . isValid $ Neg Top,
    maybe
      False
      (1 `elem`)
      (sat (P 1)),
    isNothing $
      sat $
        P 1 `Conj` Neg (P 1),
    sat (P 1 `Conj` Neg (P 2)) == Just [1],
    satisfies [1000] $ Dis $ map P [0 .. 100000000000000000000]
  ]

tooTricky :: Form
tooTricky = Con $ map (Neg . P) [1 .. 1000]

type AssignmentF = Integer -> Bool

allAssignmentsForF :: [Integer] -> [AssignmentF]
allAssignmentsForF xs = [(`elem` l) | l <- allAssignmentsFor xs]

-- The type Integer -> Bool is much more mathematically elegant, but has the
-- significant disadvantage of not implementing Show and having arbitrarily high
-- complexity. On the other hand [Integer] always has O(n) evaluation of
-- proposition letters but is a bit more messy and allows for double proposition
-- letters. An implementation that is in between the two is Set Integer. This
-- has O(log n) evaluation and does not allow for double proposition letters.
