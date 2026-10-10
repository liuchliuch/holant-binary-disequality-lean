import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinEightRMValues.Value0
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinEightRMValues.Value1
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinEightRMValues.Value2
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinEightRMValues.Value3
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinEightRMValues.Value4
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinEightRMValues.Value5
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinEightRMValues.Value6
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinEightRMValues.Value7
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinEightRMValues
open GlobalCloseCompletionKleinEightRMData
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
theorem value (s b : Fin 8) (x : Fin 8→Bool) : source s b (word s b x)=2*correction s x*rm x := by
  fin_cases s
  · exact Value0.value b x
  · exact Value1.value b x
  · exact Value2.value b x
  · exact Value3.value b x
  · exact Value4.value b x
  · exact Value5.value b x
  · exact Value6.value b x
  · exact Value7.value b x

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinEightRMValues
