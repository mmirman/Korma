module Main where

import Prelude hiding (Monad)

class Monad m where
  (>>=) :: m s t a -> ( a -> m t v b ) -> m s v b
  return :: a -> m s s a
  
newtype State s t a = State (s -> (t,a))

instance Monad State where
  (State f) >>= mg = State $ \s -> let (t,a) = f s
                                   in case mg a of
                                     State g -> g t
  return a = State $ \s -> (s,a)