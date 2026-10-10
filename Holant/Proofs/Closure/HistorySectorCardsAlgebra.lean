import Holant.ReedMuller.CoefficientAtlas.ContractionTransport
import Holant.Marked.SupportAtlas.CardTransport
import Holant.Proofs.Closure.ClosureFactorTreeAction
import Holant.OpenNetworkComposition.BoundarySums

/-! All-arity ordered weighted attachment algebra at one SAME marked basis.
The source splice keeps its two literal binary ports and the actual changed
edge. These are analytic identities, not a basis-gadget declaration. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.HistorySectorCardsAlgebra
open Holant Holant.Tractable Holant.Marked
open Holant.OpenNetworkComposition
open scoped BigOperators

variable {K : Type*} [CommSemiring K] {n : ℕ}

def atPort (i : Fin n) (A : Kernel K) : Fin n → Kernel K :=
  fun j => if j = i then A else Signature.equality

/-- The single ordered coordinate action sums only the selected input bit. -/
theorem atPort_apply (i : Fin n) (A : Kernel K) (f : Signature K n)
    (x : Fin n → Bool) :
    Signature.coordinateAction (atPort i A) f x =
      ∑ b : Bool, A (x i) b * f (Function.update x i b) := by
  classical
  unfold Signature.coordinateAction
  rw [← (Equiv.funSplitAt i Bool).symm.sum_comp,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro b _
  have hp (z : {j : Fin n // j ≠ i} → Bool) :
      (∏ j, atPort i A j (x j) ((Equiv.funSplitAt i Bool).symm (b,z) j)) =
        A (x i) b * (if (fun j : {j : Fin n // j ≠ i} => x j) = z then 1 else 0) := by
    rw [Fintype.prod_eq_mul_prod_subtype_ne _ i]
    have hz : (∏ j : {j : Fin n // j ≠ i},
        atPort i A j.val (x j.val) ((Equiv.funSplitAt i Bool).symm (b,z) j.val)) =
        if (fun j : {j : Fin n // j ≠ i} => x j) = z then 1 else 0 := by
      calc
        _ = ∏ j : {j : Fin n // j ≠ i}, Signature.equality (x j.val) (z j) := by
          apply Finset.prod_congr rfl
          intro j _
          simp [atPort,Equiv.funSplitAt_symm_apply,j.property]
        _ = _ := by simp [Signature.equality,Fintype.prod_boole,←funext_iff]
    rw [hz]
    simp [atPort,Equiv.funSplitAt_symm_apply]
  simp_rw [hp]
  rw [Fintype.sum_eq_single (fun j : {j : Fin n // j ≠ i} => x j)]
  · simp only [ite_true,mul_one]
    congr 2
  · intro z hz
    simp [Ne.symm hz]

/-- One binary table joins the selected port through the displayed kernel.
Port zero is the exposed binary endpoint; port one is the internal endpoint. -/
def weightedSplice (E B : Kernel K) (f : Signature K n) (i : Fin n) : Signature K n :=
  Signature.coordinateAction (atPort i (Kernel.mul B E)) f

theorem weightedSplice_apply (E B : Kernel K) (f : Signature K n) (i : Fin n)
    (x : Fin n → Bool) : weightedSplice E B f i x =
      ∑ a : Bool, ∑ b : Bool,
        f (Function.update x i a) * B (x i) b * E b a := by
  rw [weightedSplice,atPort_apply]
  simp only [Kernel.mul,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem weightedSplice_native (B : Kernel K) (f : Signature K n) (i : Fin n) :
    weightedSplice Signature.disequality B f i =
      spliceTensor f (fun x => B (x 0) (x 1)) i := by
  funext x
  rw [weightedSplice_apply]
  unfold spliceTensor
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one]
  congr 1
  cases a <;> cases b <;> rfl

theorem atPort_conjugate (U : InvertibleKernel) (i : Fin n) (B : Mat)
    (f : Signature AlgebraicComplex n) :
    U.symm.action (weightedSplice Signature.disequality B f i) =
      weightedSplice (sectorEdge U) (transport U B) (U.symm.action f) i := by
  change Signature.coordinateAction (fun _ => U.inverse)
      (Signature.coordinateAction (atPort i (Kernel.mul B Signature.disequality)) f) = _
  have hf : f = U.action (U.symm.action f) := (U.action_symm_action f).symm
  conv_lhs => rw [hf]
  change Signature.coordinateAction (fun _ => U.inverse)
      (Signature.coordinateAction (atPort i (Kernel.mul B Signature.disequality))
        (Signature.coordinateAction (fun _ => U.matrix) (U.symm.action f))) = _
  rw [Signature.coordinateAction_comp,Signature.coordinateAction_comp]
  unfold weightedSplice
  congr 1
  funext j
  by_cases hj : j = i
  · simp only [atPort,hj,ite_true]
    rw [transport_mul_edge]
    rfl
  · simp only [atPort,hj,ite_false,Kernel.mul_equality,U.inverse_matrix]

/-- Arbitrary residual arity and the exact ordered surviving ports. -/
theorem contract_transport (U : InvertibleKernel) (E : Mat)
    (f : Signature AlgebraicComplex (n+2)) :
    U.symm.action (Signature.contract E f) =
      Signature.contract (Kernel.pullback E U.matrix) (U.symm.action f) := by
  have h := Holant.ReedMuller.CoefficientAtlas.coordinateAction_contract
    U.matrix E (U.symm.action f)
  change Signature.contract E (U.action (U.symm.action f)) =
    U.action (Signature.contract (Kernel.pullback E U.matrix) (U.symm.action f)) at h
  rw [U.action_symm_action] at h
  exact (congrArg U.symm.action h).trans (U.symm_action_action _)

theorem reindex_transport (U : InvertibleKernel) (e : Equiv.Perm (Fin n))
    (f : Signature AlgebraicComplex n) :
    U.symm.action (Tensor.reindex e f) = Tensor.reindex e (U.symm.action f) :=
  Holant.ReedMuller.CoefficientAtlas.coordinateAction_reindex U.inverse e f

end Holant.LocalDrafts.RemoteWork.StableClosureV2.HistorySectorCardsAlgebra
end
