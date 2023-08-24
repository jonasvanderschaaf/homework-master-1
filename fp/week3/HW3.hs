{-# LANGUAGE ScopedTypeVariables #-}

module HW3 where

import Test.QuickCheck

-- * Question 1: Folding

{-
Can foldl or foldr work on infinite lists?

foldr works on infinite lists. This is because for functions f which are
non-strict in their second argument `foldr f x xs` can terminate for any object
`xs` implementing the typeclass foldable whereas foldl will not because it will
first evaluate foldl for the rest of the list before performing the computation
with the first element.

An example query and output:

ghci> l = repeat False ghci> foldr (&&) True l False

ghci> foldl (&&) True l \^CInterrupted. (infinite loop)

...
-}

-- * Question 2: Pretty Trees

data Tree a = T a [Tree a]
  deriving (Eq, Ord, Show)

exampleTree :: Tree Int
exampleTree =
  T
    23
    [ T
        11
        [ T 3 [],
          T 7 []
        ],
      T
        12
        [ T 4 [],
          T 8 [T 3 [], T 3 [], T 2 []]
        ]
    ]

ppT :: (Show a) => Tree a -> IO ()
ppT = helperPPT 0
  where
    helperPPT n (T a ts) = do
      putStrLn $ makeLine n a
      mapM_ (helperPPT (n + 1)) ts
    makeLine n a = concat (replicate n ". ") ++ show a

-- * Question 3: Arbitrary Trees

instance (Arbitrary a) => Arbitrary (Tree a) where
  arbitrary = sized randomTree
    where
      randomTree 0 = T <$> arbitrary <*> return []
      randomTree n = do
        l <- arbitrary :: Gen (NonNegative Int)
        let l' = getNonNegative l
        T <$> arbitrary <*> sequence [randomTree (n `div` l') | _ <- [1 .. l']]

-- * Question 4: Applicative Trees

instance Functor Tree where
  fmap f (T a ts) = T (f a) (fmap (fmap f) ts)

instance Applicative Tree where
  pure x = T x (repeat $ pure x)
  (<*>) (T f tfs) (T x txs) = T (f x) (zipWith (<*>) tfs txs)

{-

(i)
Claim: fmap id == id
That is, for any (t :: Tree a) we want to show that fmap id t == id t.
Proof:
Take any t = T x ts.
As induction hypothesis, assume we have
  fmap id t1 == id t1
for any t1 in ts.
Then we have:

fmap id (T x ts)
==                                (def of fmap)
T (id x) (fmap (fmap id) ts)
==                                (put your justification here)
T x [fmap id t1 | t1 <- ts]
==
T x [t1 | t1 <- ts]
==
T x ts
==
id (T x ts)

(ii)
Claim: fmap (f.g) == fmap f . fmap g
Proof:
Take any t = T x ts.
As induction hypothesis, assume we have
  fmap (f . g) t1 == (fmap f) . (fmap g) t1
for any t1 in ts.
Then we have:
(fmap f) . (fmap g) (T x ts)
==
(fmap f) (T (g x) fmap (fmap g) ts)
==
T (f (g x)) (fmap (fmap f) (fmap (fmap g) ts))
==
T ((f . g) x) (fmap (fmap f) [fmap g t1 | t1 <- ts])
==
T ((f . g) x) ((fmap f . fmap g) t1 | t1 <- ts)
==
T ((f . g) x) [fmap (f . g) t1 | t1 <- ts]
==
T ((f . g) x) fmap (fmap (f . g)) ts
==
fmap (f . g) (T x ts)

(iii)
Claim: fmap f == (pure f <*>)
Proof:
Take any t= T x ts
as induction hypothesis assume the statement holds for all t1 in ts.

Then

pure f <*> (T x ts)
==
T f (repeat (pure f)) <*> T x ts
==
T (f x) (zipWith <*> (repeat $ pure f) ts)
==
T (f x) ([tf <*> t1] | (tf, t1) <- zip (repeat $ pure f) ts)
==
T (f x) [pure f <*> t1 | t1 <- ts]
==
T (f x) [fmap f t1 | t1 <- ts]
==
T (f x) (fmap (fmap f)) ts
==
fmap f (T x ts)

Therefore
(pure f <*>) = fmap f

(iv)
Claim: pure id <*> == id
pure id <*>
== fmap id
== id

(v)
Claim: pure (.) <*> f <*> g <*> x == f <*> (g <*> x)
Proof:
Take any
x = T x' xs
f = T f' fs
g = T g' gs
as induction hypothesis assume the statement holds for all x1 in xs and f,g.

pure (.) <*> f <*> g <*> x
==
((pure (.) <*> f) <*> g) <*> x
==
((fmap (.) f) <*> g) <*> x
==
((T (f' .) [fmap (.) f1 | f1 <- fs]) <*> T g' gs) <*> x
==
((T (f' . g') [fmap (.) f1 <*> g1 | (f1,g1) <- zip fs gs])) <*> x
==
(T ((f' . g') x) [fmap (.) f1 <*> g1 <*> x1 | ((f1, g1), x1) <- zip (zip fs gs) xs])
==
(T (f' (g' x)) [fmap (.) f1 <*> g1 <*> x1 | ((f1, g1), x1) <- zip fs (zip gs xs)])
==
(T (f' (g' x)) [pure (.) <*> f1 <*> g1 <*> x1 | ((f1, g1), x1) <- zip fs (zip gs xs)])
== (IH)
(T (f' (g' x)) [f1 <*> (g1 <*> x1) | (f1, (g1, x1)) <- zip fs (zip gs xs)])
==
(T f' fs) <*> (T (g' x) [g1 <*> x1 | (g1, x1) <- zip gs xs])
==
(T f' fs) <*> ((T g' gs) <*> (T x' xs))
==
f <*> (g <*> x)

(vi)
Claim: pure f <*> pure x == pure (f x)
Proof: We prove by induction that `treeEqUpto n` will give true for all n. This
gives that both trees are indeed equal.

For n=0 the statement is trivially true because treeEqUpTo 0 always returns 0.

Now for the induction step. Suppose the statement is true for n. Then

treeEqUpTo (n+1) (pure f <*> pure x) (pure (f x))
== treeEqUpTo (n+1) ((T f (repeat pure f)) <*> (T x (repeat pure x))) (T (f x) (repeat (pure (f x))))
== (repeat (pure (f x))))
== (f x == f x) && and [treeEqUpTo n (repeat (pure f <*> pure x)) (repeat (pure (f x))) | _ <- 1..n+1]
== (f x == f x) && and [True | _ <- 1..n+1] (By IH)
== True && True

(vii)
Claim: u <*> pure y == pure ($ y) <*> u
Proof:
Take any u = T f fs as induction hypothesis assume the statement holds for all
f1 in fs.

(T f fs) <*> pure y
==
(T f fs) <*> T (y) (repeat (pure y))
==
T (f y) [f1 <*> pure y | f1 <- fs]
== (IH)
T (($ y) f) [pure ($ y) <*> f1 | f1 <- fs]
==
pure ($ y) <*> (T f fs)

-}

treeEqUpto :: (Eq a) => Int -> Tree a -> Tree a -> Bool
treeEqUpto 0 _ _ = True
treeEqUpto k (T x xts) (T y yts) = x == y && and (take k $ zipWith (treeEqUpto (k - 1)) xts yts)

-- * Question 5: Applicatives as lax monoidal functors

phi :: forall f a b. (Applicative f) => (f a, f b) -> f (a, b)
phi = up . right . down
  where
    down = swap . fmap (fmap (,)) . swap
    right = swap . fmap (<*>) . swap
    up = uncurry ($)
    swap (a, b) = (b, a)

-- * Question 6: Hello World 3.0

dialogue :: IO ()
dialogue = do
  putStrLn "Hello! Who are you?"
  name <- getLine
  putStrLn $ "Nice to meet you, " ++ name ++ "!"
  putStrLn "How old are you?"
  age :: Integer <- fmap read getLine
  if age < 100
    then putStrLn $ "Ah, that is " ++ show (100 - age) ++ " years younger than me!"
    else
      if age == 100
        then putStrLn "Ah, that is the same age as I am!"
        else putStrLn $ "Ah, that is " ++ show (age - 100) ++ " years older than me!"
