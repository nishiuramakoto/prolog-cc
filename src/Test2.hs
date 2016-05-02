
import Prelude
data CCPrologGT state n m a  =  CCPrologGT  state n m a

type CCPrologT site m a = CCPrologGT Int (CCPrologT site m) m a
