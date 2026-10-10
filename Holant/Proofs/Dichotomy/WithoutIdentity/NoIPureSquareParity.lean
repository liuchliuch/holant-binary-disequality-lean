import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPureSquareResources
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPureSquareData
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPureOddSource

/-! Universal parity support in the actual native graph closure, after
retaining both the whole-family tract exit and exact controlled hardness.
The negative tract guard is essential: affine full unaries are non-parity. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureSquareParity
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
set_option Elab.async false
variable (target : NoIOrdinaryRaw.Target) (D : NoIPureSquareData.Data target)
local instance : Algebra ℚ D.K:=D.K.algebra'


theorem eq4_form : (eq4 target D).network.denote=NoIPureEqualityCap.pure (1 : D.K) 1 := by
  rw [eq4,Network.denote_corolla]
  funext x
  cases h0:x 0 <;>cases h1:x 1 <;>cases h2:x 2 <;>cases h3:x 3 <;>
    simp [Holant.EightVertex.ProductAnchor.equalityFour,NoIPureEqualityCap.pure,
      funext_iff,Fin.forall_fin_succ,h0,h1,h2,h3]

def Positive : Prop:=Tract (familyAction sourceKBasis
  (GlobalCloseCompletionUnaryDescentSource.ambient D.K D.table))
def GraphParity : Prop:=∀n,∀N : O.Output D.table n,NoIPureOddFace.UniformParity N.network.denote

theorem mixed {n : ℕ} (N : O.Output D.table n) (nonparity : ¬NoIPureOddFace.UniformParity N.network.denote) :
    Positive target D ∨ target.Hard := by
  rcases NoIPureOddSource.classified D.K D.table D.F (pins target D) (pins_form target D)
    (eq4 target D) 1 1 one_ne_zero one_ne_zero (eq4_form target D) N nonparity with tract|hard
  · exact Or.inl tract
  · exact Or.inr (NoIOrdinaryRaw.Target.Hard.compose
      (S:=NoISuppliedIdentityConsumer.target D.K D.table D.F) (T:=target) hard D.back)

theorem graph {n : ℕ} (noHard : ¬target.Hard) (negative : ¬Positive target D)
    (N : O.Output D.table n) : NoIPureOddFace.UniformParity N.network.denote := by
  by_contra bad
  exact noHard ((mixed target D N bad).resolve_left negative)

theorem classified : Positive target D ∨ target.Hard ∨ GraphParity target D := by
  classical
  by_cases positive:Positive target D
  · exact Or.inl positive
  by_cases hard:target.Hard
  · exact Or.inr (Or.inl hard)
  · exact Or.inr (Or.inr (fun _ N=>graph target D hard positive N))

theorem noHard (negative : ¬target.Hard) : Positive target D ∨ GraphParity target D := by
  rcases classified target D with tract|hard|parity
  · exact Or.inl tract
  · exact False.elim (negative hard)
  · exact Or.inr parity


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureSquareParity
end
