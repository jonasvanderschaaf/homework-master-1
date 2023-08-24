{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}

module HW5 where

-- * Question 1: From LensR to Lens'

type Lens' s a = forall f. (Functor f) => (a -> f a) -> s -> f s

data LensR s a = L
  { viewR :: s -> a,
    setR :: a -> s -> s,
    modifyR :: (a -> a) -> s -> s
  }

newtype Identity a = Id a

instance Functor Identity where fmap f (Id x) = Id (f x)

runIdentity :: Identity a -> a
runIdentity (Id x) = x

set :: Lens' s a -> a -> s -> s
set ln x = runIdentity . ln (Id . const x)

modify :: Lens' s a -> (a -> a) -> s -> s
modify ln f = runIdentity . ln (Id . f)

newtype Const v a = Co v

instance Functor (Const v) where fmap _ (Co x) = Co x

runConst :: Const v a -> v
runConst (Co x) = x

view :: Lens' s a -> s -> a
view ln = runConst . ln Co

lensToLensR :: Lens' s a -> LensR s a
lensToLensR ln =
  L
    { viewR = view ln,
      setR = set ln,
      modifyR = modify ln
    }

lensRtoLens :: LensR s a -> Lens' s a
lensRtoLens lnr x y = fmap (flip (setR lnr) y) t
  where
    z = viewR lnr y
    t = x z

-- * Question 2: Manual Raise

data Person = P {name :: String, salary :: Int} deriving (Eq, Show)

lname :: Lens' Person String
lname elt_fn (P n s) = fmap (`P` s) (elt_fn n)

lsalary :: Lens' Person Int
lsalary elt_fn (P n s) = fmap (P n) (elt_fn s)

fred :: Person
fred = P "Fred" 100

{-
  modify salary (+40) (P "Fred" 100)
==                                                   {def of modify}
  ???
==
  .
  .
  .
==                                                   {def of runIdentity}
  P "Fred" 140
-}

-- * Question 3: ListPos to Zipper to ListPos

data ListPos a = LP [a] Int deriving (Eq, Show)

myPos :: ListPos String
myPos = LP ["Kwik", "Kwek", "Kwak", "Tick", "Trick", "Track"] 3

data Zipper a = Zip [a] a [a] deriving (Eq, Show)

class Convertable a b where
  convert :: a -> b

instance Convertable (ListPos a) (Zipper a) where
  convert (LP xs n) = Zip ys y ys'
    where
      ys = reverse $ take n xs
      y = xs !! n
      ys' = drop (length xs - n + 1) xs

instance Convertable (Zipper a) (ListPos a) where
  convert (Zip xs x xs') = LP (reverse xs ++ x : xs') (length xs)

-- * Question 4: Tree Zip

data Tree a = Node a [Tree a] deriving (Eq, Show)

data TreePos a = TP (Tree a) [Int] deriving (Eq, Show)

myTree :: Tree String
myTree =
  Node
    "food"
    [ Node
        "cheese"
        [ Node "kaas" [],
          Node "Käse" []
        ],
      Node
        "bread"
        [ Node "brood" [],
          Node "Brot" []
        ]
    ]

class TreeLike t where
  -- | Create a single node.
  single :: a -> t a

  -- | Get the item at the point.
  getItem :: t a -> a

  -- | Move down to child number k.
  moveToChild :: Int -> t a -> t a

  -- | Move up to the parent, assuming we are not at the root.
  moveUp :: t a -> t a

  -- | Insert a value as a new left-most child of the point.
  insertChild :: a -> t a -> t a

  -- | Remove the point (and its subtree) and move up, assuming we are not at the root.
  remove :: t a -> t a

instance TreeLike TreePos where
  single x = TP (Node x []) []
  getItem = undefined -- Change this!
  moveToChild k (TP t ks) = TP t (ks ++ [k])
  moveUp (TP _ []) = error "Cannot move above root!"
  moveUp (TP t (_ : ks)) = TP t ks
  insertChild = undefined -- Change this!
  remove = undefined -- Change this!

newtype Path a = Step a -- Change this!
  deriving (Eq, Show)

newtype ZipTree a = ZT a -- Change this!
  deriving (Eq, Show)

instance TreeLike ZipTree where
  single = undefined
  getItem = undefined
  moveToChild = undefined
  moveUp = undefined
  insertChild = undefined
  remove = undefined

-- * Question 5: Speculation

{-

... write at least five sentences ...

-}
