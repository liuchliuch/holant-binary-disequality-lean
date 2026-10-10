import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPureLegalAffineSource
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPureLegalSupport
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPureSquareFour

/-! All closure premises of the phase selector are produced from the genuine
native target's nonhardness and the unchanged whole-family negative criterion. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureGraphGuards
open Holant Holant.Tractable Holant.Algebraic
namespace C
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEONegativeClosedSupport (Closed)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
set_option Elab.async false
variable (target : NoIOrdinaryRaw.Target) (D : NoIPureSquareData.Data target)
local instance : Algebra ℚ D.K := D.K.algebra'
variable (noHard : ¬target.Hard) (negative : ¬NoIPureSquareFour.Positive target D)

include negative in
theorem nonproduct : ¬NoIPureProductPositive.WholeProduct target D :=
  fun h => negative (NoIPureProductPositive.positive target D h).tract

include noHard negative in
theorem uniform : NoIPureSquareFour.GraphFour target D :=
  fun _ N => NoIPureSquareFour.graph target D noHard negative N

include noHard negative in
theorem graph {n : ℕ} (N : NativeAntiTargetSource.Output D.table n) :
    C.Closed (fun z => (N.network.denote z : AlgebraicComplex)) ∧
    NoIPureChargeTwoFamily.UniformFour (fun z => (N.network.denote z : AlgebraicComplex)) ∧
    NoIPurePhaseLegalAffine.LegalAffine (fun z => (N.network.denote z : AlgebraicComplex)) := by
  have legal := NoIPureLegalAffineSource.graph target D (nonproduct target D negative)
    (uniform target D noHard negative) noHard N
  refine ⟨NoIPureLegalSupport.closed _ legal,?_,legal⟩
  intro x y hx hy
  apply uniform target D noHard negative n N x y
  · intro h
    apply hx
    simp [h]
  · intro h
    apply hy
    simp [h]

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureGraphGuards
end
