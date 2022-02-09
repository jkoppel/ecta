module Application.TermSearch.Type
  ( ExportType(..)
  , Benchmark(..)
  , ArgType
  ) where

import           Data.Text                      ( Text )
import GHC.Generics
import Data.Hashable

import           Data.ECTA
import           Data.ECTA.Term

data ExportType
  = ExportVar Text
  | ExportFun ExportType ExportType
  | ExportCons Text [ExportType]
  | ExportForall Text ExportType
  deriving (Eq, Ord, Show, Read, Generic)

instance Hashable ExportType

data Benchmark = Benchmark Text Int String ([(Text, ExportType)], ExportType)
  deriving (Eq, Ord, Show, Read)

type ArgType = (Symbol, Node)
