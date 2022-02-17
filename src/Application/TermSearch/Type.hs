module Application.TermSearch.Type
  ( ExportType(..)
  , Benchmark(..)
  , ArgType
  , Mode(..)
  ) where

import           Data.Data                      ( Data )
import           Data.Hashable                  ( Hashable )
import           Data.Text                      ( Text )
import           GHC.Generics                   ( Generic )

import           Data.ECTA
import           Data.ECTA.Term

data ExportType
  = ExportVar Text
  | ExportFun ExportType ExportType
  | ExportCons Text [ExportType]
  | ExportForall Text ExportType
  deriving (Eq, Ord, Show, Read, Data, Generic)

instance Hashable ExportType

data Benchmark = Benchmark Text Int Term ([(Text, ExportType)], ExportType)
  deriving (Eq, Ord, Show, Read)

type ArgType = (Symbol, Node)

data Mode
  = Normal
  | HKTV
  | Lambda
  deriving (Eq, Ord, Show, Data, Generic)