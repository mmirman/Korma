module Utils where

import Data.Functor ((<$>))

infixr 0 <$>>

(<$>>):: Functor f => (a -> b) -> f a  -> f b
(<$>>) = (<$>)