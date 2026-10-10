import Holant.Dihedral.TwoCardLocalization.ResidualOrder
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinHigherNonaffineMatchingGroup

/-! Exact Pauli closure for the recorded physical contraction programs.
The hypothesis on an ancestor consists only of its actual single-pair cards.
Every nonempty program starts with one such card, and all remaining steps
preserve matching products, including vanishing cycle traces. -/
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffine
noncomputable section
open Holant.Dihedral.TwoCardLocalization
open Holant.Certificates.MatchingContractionClosure
open Holant.Dihedral.CompatibleClosure

namespace RulingProgram

def liftCore {I : Type*} {n m : ℕ} : Program I n m → Program I (n+2) (m+2)
  | .done n => .done (n+2)
  | .step p i rest => .step (outsideOrder p) i (liftCore rest)

@[simp] theorem liftCore_length {I : Type*} {n m : ℕ} (P : Program I n m) :
    (liftCore P).length = P.length := by
  induction P with
  | done n => rfl
  | step p i rest ih => simp only [liftCore,Program.length,ih]

theorem liftCore_residual {K I : Type*} [Field K] (C : I → Kernel K)
    {n m : ℕ} (P : Program I n m) (q : Signature K (n+2)) :
    (liftCore P).residual C q = P.core C q := by
  induction P with
  | done n => rfl
  | step p i rest ih => exact ih _

end RulingProgram

namespace MatchingCard

theorem pairOrder_zero_one (n : ℕ) :
    pairOrder (0 : Fin (n+2)) 1 = Equiv.refl _ := by
  simp [pairOrder]

theorem contractPair_front {n : ℕ} (C : Kernel ℂ) (q : Signature ℂ (n+2)) :
    Tensor.reindex (remainingOrder 0 1 Fin.zero_ne_one).symm (contractPair 0 1 C q) =
      Signature.contract C q := by
  have he := contractPair_order (0 : Fin (n+2)) 1 Fin.zero_ne_one C q
  rw [pairOrder_zero_one] at he
  exact he

theorem Pauli_reindex {P Q : Type*} (e : P ≃ Q) (q : Tensor ℂ P)
    (hq : PauliMatchingOrZero q) : PauliMatchingOrZero (Tensor.reindex e q) :=
  (Pauli_iff_group _).mpr (((Pauli_iff_group _).mp hq).reindex e)

theorem Pauli_reindex_iff {P Q : Type*} (e : P ≃ Q) (q : Tensor ℂ P) :
    PauliMatchingOrZero (Tensor.reindex e q) ↔ PauliMatchingOrZero q := by
  constructor
  · intro h
    have hh := Pauli_reindex e.symm _ h
    have he : Tensor.reindex e.symm (Tensor.reindex e q) = q := by
      funext x
      simp only [Tensor.reindex,Equiv.symm_apply_apply]
    rwa [he] at hh
  · exact Pauli_reindex e q

theorem Pauli_contract {n : ℕ} (q : Signature ℂ (n+2)) (a : Label)
    (hq : PauliMatchingOrZero q) : PauliMatchingOrZero (Signature.contract (dual a) q) := by
  have h := contractPair_closed binaryGroup_projective X_mem binaryGroup_reversal
    (0 : Fin (n+2)) 1 Fin.zero_ne_one (asMatrix (dual a)) (dual_safe a) q
    ((Pauli_iff_group _).mp hq)
  have hh := Pauli_reindex (remainingOrder 0 1 Fin.zero_ne_one).symm _ ((Pauli_iff_group _).mpr h)
  have he := contractPair_front (dual a) q
  change PauliMatchingOrZero
    (Tensor.reindex (remainingOrder 0 1 Fin.zero_ne_one).symm (contractPair 0 1 (dual a) q)) at hh
  rwa [he] at hh

theorem Pauli_program {I : Type*} (labels : I → Label) {n m : ℕ} (P : Program I n m)
    (q : Signature ℂ n) (hq : PauliMatchingOrZero q) :
    PauliMatchingOrZero (P.residual (fun i => dual (labels i)) q) := by
  induction P with
  | done n => exact hq
  | step p i rest ih =>
    exact ih _ (Pauli_contract _ _ (Pauli_reindex p.symm q hq))

/-- Every ordered physical pair and every residual-port order are included.
No safety condition is imposed on the uncontracted ancestor itself. -/
def OrderedPairSafe {n : ℕ} (q : Signature ℂ (n+2)) : Prop :=
  ∀ p : Equiv.Perm (Fin (n+2)), ∀ a : Label,
    PauliMatchingOrZero (Signature.contract (dual a) (Tensor.reindex p.symm q))

theorem orderedPairSafe_reindex {n : ℕ} (q : Signature ℂ (n+2))
    (hq : OrderedPairSafe q) (p : Equiv.Perm (Fin (n+2))) :
    OrderedPairSafe (Tensor.reindex p.symm q) := by
  intro e a
  exact hq (e.trans p) a

/-- Positive program length is essential: the ancestor need not itself be a
matching product. The first literal contraction supplies the safe tensor. -/
theorem orderedPairSafe_program {I : Type*} (labels : I → Label) {n m : ℕ}
    (P : Program I (n+2) m) (hP : 0 < P.length) (q : Signature ℂ (n+2))
    (hq : OrderedPairSafe q) : PauliMatchingOrZero (P.residual (fun i => dual (labels i)) q) := by
  cases P with
  | done n => simp only [Program.length] at hP; omega
  | step p i rest => exact Pauli_program labels rest _ (hq p (labels i))

theorem orderedPairSafe_core {I : Type*} (labels : I → Label) {n m : ℕ}
    (P : Program I n m) (hP : 0 < P.length) (q : Signature ℂ (n+2))
    (hq : OrderedPairSafe q) : PauliMatchingOrZero (P.core (fun i => dual (labels i)) q) := by
  rw [←RulingProgram.liftCore_residual]
  apply orderedPairSafe_program labels (RulingProgram.liftCore P) _ q hq
  simpa only [RulingProgram.liftCore_length] using hP

end MatchingCard
end
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffine
