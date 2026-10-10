import Holant.Marked.SupportAtlas.Deck
import Holant.Marked.Dictionary
import Holant.Projective.CyclicQuaternary.Physical

/-! Exact ordered finite-sum transport of the physical two-edge card, for an
arbitrary invertible analytic basis. No card normalization identity is assumed. -/
noncomputable section
set_option maxHeartbeats 2000000
namespace Holant.Marked.SupportAtlas
open Holant.Tractable
open Holant.Projective.CyclicQuaternary.Physical (sum_words4)

def permuteWord (e : Equiv.Perm (Fin 4)) (x : Word) : Word := fun j => x (e.symm j)

def wordPermutation (e : Equiv.Perm (Fin 4)) : Word ≃ Word where
  toFun := permuteWord e
  invFun := permuteWord e.symm
  left_inv x := by funext j; simp [permuteWord]
  right_inv x := by funext j; simp [permuteWord]

def reorder (q : Signature Scalar 4) (e : Equiv.Perm (Fin 4)) : Signature Scalar 4 :=
  fun x => q (permuteWord e x)

theorem coordinateAction_reorder (M : Mat) (q : Signature Scalar 4)
    (e : Equiv.Perm (Fin 4)) :
    Signature.coordinateAction (fun _ => M) (reorder q e) =
      reorder (Signature.coordinateAction (fun _ => M) q) e := by
  funext x
  change (∑ y : Word, (∏ j, M (x j) (y j)) * q (permuteWord e y)) =
    ∑ y : Word, (∏ j, M (permuteWord e x j) (y j)) * q y
  rw [← (wordPermutation e).sum_comp (fun y : Word =>
    (∏ j, M (permuteWord e x j) (y j)) * q y)]
  apply Finset.sum_congr rfl
  intro y _
  congr 1
  exact (e.symm.prod_comp (fun j => M (x j) (y j))).symm

def contract0 (q : Signature Scalar 4) (E : Mat) : Mat :=
  fun u v => ∑ a : Bool, ∑ b : Bool, E a b * q ![a,b,u,v]

/-- The two remaining ports keep their exact matrix action after contracting the first two. -/
theorem contract0_coordinateAction (M E : Mat) (q : Signature Scalar 4) :
    contract0 (Signature.coordinateAction (fun _ => M) q) E =
      Kernel.mul (Kernel.mul M (contract0 q (Kernel.pullback E M))) (Kernel.transpose M) := by
  funext u v
  simp [contract0, Signature.coordinateAction, sum_words4, Fin.prod_univ_succ,
    Kernel.pullback, Kernel.mul, Kernel.transpose]
  ring

theorem transport_forward (U : InvertibleKernel) (C : Mat) :
    transport U (Kernel.mul (Kernel.mul U.matrix C) (Kernel.transpose U.matrix)) = C := by
  simp only [transport, Kernel.mul_assoc]
  rw [← Kernel.mul_assoc U.inverse U.matrix, U.inverse_matrix, Kernel.equality_mul,
    transpose_matrix_inverse, Kernel.mul_equality]

theorem transport_contract0 (U : InvertibleKernel) (q : Signature Scalar 4) (E : Mat) :
    transport U (contract0 q E) =
      contract0 (U.symm.action q) (Kernel.pullback E U.matrix) := by
  calc
    _ = transport U (contract0 (U.action (U.symm.action q)) E) := by rw [U.action_symm_action]
    _ = _ := by rw [InvertibleKernel.action, contract0_coordinateAction, transport_forward]

/-- Actual physical attachment of the two ordered binary ports through two native X edges. -/
def physicalCard (q : Signature Scalar 4) (e : Equiv.Perm (Fin 4)) (B : Mat) : Mat :=
  contract0 (reorder q e) (Kernel.mul (Kernel.mul Signature.disequality B) Signature.disequality)

theorem effective_transport (U : InvertibleKernel) (B : Mat) :
    Kernel.pullback (Kernel.mul (Kernel.mul Signature.disequality B) Signature.disequality) U.matrix =
      Kernel.mul (Kernel.mul (sectorEdge U) (transport U B)) (sectorEdge U) := by
  simp only [sectorEdge, transport, Kernel.pullback, Kernel.mul_assoc]
  rw [← Kernel.mul_assoc U.matrix U.inverse, U.matrix_inverse, Kernel.equality_mul,
    ← Kernel.mul_assoc (Kernel.transpose U.inverse) (Kernel.transpose U.matrix),
    transpose_inverse_matrix, Kernel.equality_mul]

/-- Full card transport, at every original ordered port permutation. -/
theorem physicalCard_transport (U : InvertibleKernel) (q : Signature Scalar 4)
    (e : Equiv.Perm (Fin 4)) (B : Mat) :
    transport U (physicalCard q e B) = contract0 (reorder (U.symm.action q) e)
      (Kernel.mul (Kernel.mul (sectorEdge U) (transport U B)) (sectorEdge U)) := by
  rw [physicalCard, transport_contract0, effective_transport]
  congr 1
  exact coordinateAction_reorder U.inverse q e

end Holant.Marked.SupportAtlas
