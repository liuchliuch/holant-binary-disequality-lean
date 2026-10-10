import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPureGraphPredicates
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPureSquareParity
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPureChargeTwoFamily

/-! Every actual native graph has support in one weight class modulo four
after the full-family tract and controlled hardness alternatives are retained. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureSquareFour
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
namespace O
export NativeAntiTargetSource (Output)
end O
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
set_option Elab.async false
variable (target : NoIOrdinaryRaw.Target) (D : NoIPureSquareData.Data target)
local instance : Algebra ℚ D.K:=D.K.algebra'

abbrev Positive : Prop:=NoIPureSquareParity.Positive target D

theorem mixed {n : ℕ} (N : O.Output D.table n)
    (different : ¬NoIPureChargeTwoFamily.UniformFour N.network.denote) :
    Positive target D ∨ target.Hard := by
  rcases NoIPureChargeTwoFamily.classified D.K D.table D.F
    (NoIPureSquareParity.pins target D) (NoIPureSquareParity.pins_form target D)
    (NoIPureSquareParity.eq4 target D) 1 1 one_ne_zero one_ne_zero
    (NoIPureSquareParity.eq4_form target D) N different with tract|hard
  · exact Or.inl tract
  · exact Or.inr (NoIOrdinaryRaw.Target.Hard.compose
      (S:=NoISuppliedIdentityConsumer.target D.K D.table D.F) (T:=target) hard D.back)

theorem graph {n : ℕ} (noHard : ¬target.Hard) (negative : ¬Positive target D)
    (N : O.Output D.table n) : NoIPureChargeTwoFamily.UniformFour N.network.denote := by
  by_contra bad
  exact noHard ((mixed target D N bad).resolve_left negative)

theorem classified : Positive target D ∨ target.Hard ∨ GraphFour target D := by
  classical
  by_cases positive:Positive target D
  · exact Or.inl positive
  by_cases hard:target.Hard
  · exact Or.inr (Or.inl hard)
  · exact Or.inr (Or.inr (fun _ N=>graph target D hard positive N))

theorem noHard (negative : ¬target.Hard) : Positive target D ∨ GraphFour target D := by
  rcases classified target D with tract|hard|four
  · exact Or.inl tract
  · exact False.elim (negative hard)
  · exact Or.inr four


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureSquareFour
end
