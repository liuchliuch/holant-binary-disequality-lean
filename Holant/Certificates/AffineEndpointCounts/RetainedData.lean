import Holant.Certificates.AffineEndpointCounts.RetainedRouting
namespace Holant.Certificates.AffineEndpointCounts
open Holant.Certificates.AffineEndpoint
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def candidatePairs (b : Bool) : Fin 44 → SupportCatalog.SupportIndex × Nat :=
  if b then ![(204,0),(236,0),(248,0),(280,81),(284,81),(286,274),(292,81),(294,274),(298,324),(304,23),(304,62),(304,71),(304,110),(304,157),(304,227),(304,263),(304,397),(304,419),(305,7),(306,2751),(306,5470),(306,5485),(306,5491),(306,6907),(306,7087),(306,7839),(306,8895),(306,9981),(306,10167),(306,10431),(306,10750),(306,10815),(306,10892),(306,10898),(306,10913),(306,11134),(306,11703),(306,11901),(306,13983),(306,14767),(306,14971),(306,16350),(306,16365),(306,16371)] else ![(128,2),(129,3),(130,3),(131,0),(132,3),(133,0),(134,0),(135,1),(204,1),(204,21),(204,30),(205,3),(205,23),(205,24),(206,6),(206,9),(206,29),(207,0),(207,11),(207,31),(236,1),(236,21),(236,30),(237,3),(237,23),(237,24),(238,6),(238,9),(238,29),(239,0),(239,11),(239,31),(248,1),(248,21),(248,30),(249,6),(249,9),(249,29),(250,3),(250,23),(250,24),(251,0),(251,11),(251,31)]
theorem candidateBound : ∀b j, (candidatePairs b j).2 < phaseCodeCount (SupportCatalog.supportDim (candidatePairs b j).1) := by decide +kernel
def candidateInput (b : Bool) (j : Fin 44) : InputCode :=
  ⟨(candidatePairs b j).1,⟨(candidatePairs b j).2,candidateBound b j⟩⟩
def candidatePairList (b : Bool) : List (Nat × Nat) :=
  List.ofFn (fun j => ((candidatePairs b j).1.val,(candidatePairs b j).2))
theorem candidateInput_injective : ∀b, Function.Injective (candidateInput b) := by decide +kernel

end Holant.Certificates.AffineEndpointCounts
