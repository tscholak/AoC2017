module Utils

import Data.Vect

cycle : (xs : Vect (S n) a) -> Stream a
cycle (x :: xs) = x :: cycle' xs
  where cycle' : Vect n a -> Stream a
        cycle' []        = x :: cycle' xs
        cycle' (y :: ys) = y :: cycle' ys

take' : (n : Nat) -> (xs : Stream a) -> Vect n a
take' Z _ = []
take' (S n) (x :: xs) = x :: (take' n xs)

export
shift : Nat -> Vect n a -> Vect n a
shift Z xs = xs
shift (S k) [] = []
shift {n = S m} (S k) (x :: xs) = take' (S m) $ drop (S k) $ cycle (x :: xs)

export
max' : Ord a => Vect (S n) a -> a
max' (x :: xs) = foldl max x xs

export
min' : Ord a => Vect (S n) a -> a
min' (x :: xs) = foldl min x xs

export
allPairs : Vect (S n) a -> Vect (S n) (Vect n (a, a))
allPairs {n} xs = g xs n where
  f : Vect (S n) a -> Vect n (a, a)
  f (x :: xs) = map (MkPair x) xs

  g : Vect (S n) a -> (m : Nat) -> Vect (S m) (Vect n (a, a))
  g xs Z = [f xs]
  g xs (S k) = (f $ shift (S k) xs) :: g xs k
