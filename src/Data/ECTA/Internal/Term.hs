{-# LANGUAGE OverloadedStrings #-}

module Data.ECTA.Internal.Term (
    Symbol(.., Symbol)

  , Term(..)
  ) where


import Data.Hashable ( Hashable(..) )
import qualified Data.Interned as OrigInterned
import Data.Maybe ( maybeToList )
import Data.String (IsString(..) )
import Data.Text ( Text )
import qualified Data.Text as Text

import GHC.Generics ( Generic )

import Data.Interned.Text ( InternedText, internedTextId )


import Control.Lens ( (&), ix, (^?), (%~) )

import Data.ECTA.Paths
import Data.Text.Extended.Pretty

---------------------------------------------------------------
-------------------------- Symbols ----------------------------
---------------------------------------------------------------

data Symbol = Symbol' {-# UNPACK #-} !InternedText
  deriving ( Eq, Ord )

pattern Symbol :: Text -> Symbol
pattern Symbol t <- Symbol' (OrigInterned.unintern -> t) where
  Symbol t = Symbol' (OrigInterned.intern t)

instance Pretty Symbol where
  pretty (Symbol t) = t

instance Show Symbol where
  show (Symbol it) = show it

instance Hashable Symbol where
  hashWithSalt s (Symbol' t) = s `hashWithSalt` (internedTextId t)

instance IsString Symbol where
  fromString = Symbol . fromString


---------------------------------------------------------------
---------------------------- Terms ----------------------------
---------------------------------------------------------------

data Term = Term !Symbol ![Term]
  deriving ( Eq, Ord, Generic )

instance Hashable Term

instance Pretty Term where
  pretty (Term s [])            = pretty s
  pretty (Term s ts)            = pretty s <> "(" <> (Text.intercalate ", " $ map pretty ts) <> ")"
  
instance Show Term where
  show t = show (pretty t)

---------------------
------ Term ops
---------------------

instance Pathable Term Term where
  type Emptyable Term = Maybe Term

  getPath EmptyPath       t           = Just t
  getPath (ConsPath p ps) (Term _ ts) = case ts ^? ix p of
                                          Nothing -> Nothing
                                          Just t  -> getPath ps t

  getAllAtPath p t = maybeToList $ getPath p t

  modifyAtPath f EmptyPath       t           = f t
  modifyAtPath f (ConsPath p ps) (Term s ts) = Term s (ts & ix p %~ modifyAtPath f ps)