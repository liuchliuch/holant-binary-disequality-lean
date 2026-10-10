import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinSixEncodingValues.Value00
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinSixEncodingValues.Value01
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinSixEncodingValues.Value02
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinSixEncodingValues.Value03
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinSixEncodingValues.Value10
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinSixEncodingValues.Value11
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinSixEncodingValues.Value12
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinSixEncodingValues.Value13
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinSixEncodingValues.Value20
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinSixEncodingValues.Value21
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinSixEncodingValues.Value22
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinSixEncodingValues.Value23
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinSixEncodingValues.Value30
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinSixEncodingValues.Value31
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinSixEncodingValues.Value32
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinSixEncodingValues.Value33
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinSixEncodingValues
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

theorem value (e : Fin 4) (a : Fin 48) (j k : Fin 4) :
    GlobalCloseCompletionKleinSixEncoding.coefficient e a j k=
      GlobalCloseCompletionKleinSixLinearPacked.coefficient e a j k := by
  fin_cases e <;> fin_cases j
  · exact Value00.value a k
  · exact Value01.value a k
  · exact Value02.value a k
  · exact Value03.value a k
  · exact Value10.value a k
  · exact Value11.value a k
  · exact Value12.value a k
  · exact Value13.value a k
  · exact Value20.value a k
  · exact Value21.value a k
  · exact Value22.value a k
  · exact Value23.value a k
  · exact Value30.value a k
  · exact Value31.value a k
  · exact Value32.value a k
  · exact Value33.value a k

theorem encoded_card (a b c : Fin 48) (s : Fin 8) (j k : Fin 4) :
    GlobalCloseCompletionKleinSixPacked.encode (GlobalCloseCompletionKleinSixFiniteData.card a b c s j k)=
      GlobalCloseCompletionKleinSixLinearPacked.cardCode a b c s j k := by
  rw [GlobalCloseCompletionKleinSixEncoding.code_expansion]
  simp only [value]
  rfl

theorem accepted (a b c : Fin 48) (s : Fin 8) :
    GlobalCloseCompletionKleinSixPacked.accepted a b c s=
      GlobalCloseCompletionKleinSixLinearPacked.accepted a b c s := by
  simp only [GlobalCloseCompletionKleinSixPacked.accepted,
    GlobalCloseCompletionKleinSixLinearPacked.accepted,GlobalCloseCompletionKleinSixPacked.safe,
    encoded_card]


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinSixEncodingValues
