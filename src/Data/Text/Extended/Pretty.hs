module Data.Text.Extended.Pretty (
    Pretty(..)
  ) where

import Data.Text ( Text )

----------------------------------------------------------------------

class Pretty a where
  pretty :: a -> Text