import Holant.Proofs.Hardness.GeneralEOPhaseExtractionMatchingNormalForm
import Holant.Proofs.Hardness.EOBinaryPlaneCore

/-! The exact local matching-switch rule for the positive tensor-product
quaternary residual: every complete native closure is 2c or 4c. In particular,
a switch cannot create a zero or change its real phase when c is nonzero. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseExtractionPositiveSwitch
open Holant
open scoped BigOperators
namespace H
export GeneralEOPhaseExtractionLoopTomography (merge merge_denote)
end H
namespace O
export GeneralEOPinnedDescentOperations (word)
end O
namespace N
export GeneralEOPhaseExtractionClosedTomography (NativeClosure)
end N
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

def positive (c : ℂ) : Signature ℂ 4 := EOBinaryPlaneCore.lift (fun _ => c)

def assignment (e : Equiv.Perm (Fin 4)) (p : Equiv.Perm (Fin 2))
    (b d : Bool) : Fin 4 → Bool := O.word b (!b) (![d,!d] ∘ p) ∘ e

def compatible (x : Fin 4 → Bool) : Prop := x 1=!(x 0) ∧ x 3=!(x 2)
instance (x : Fin 4 → Bool) : Decidable (compatible x) := inferInstanceAs (Decidable (_ ∧ _))

def count (e : Equiv.Perm (Fin 4)) (p : Equiv.Perm (Fin 2)) : ℕ :=
  ∑b : Bool,∑d : Bool,if compatible (assignment e p b d) then 1 else 0

/-- Forty-eight finite permutation cases, reduced by the Lean kernel. -/
theorem count_two_or_four : ∀ (e : Equiv.Perm (Fin 4)) (p : Equiv.Perm (Fin 2)),
    count e p=2 ∨ count e p=4 := by decide

theorem closed_factor (c : ℂ) (e : Equiv.Perm (Fin 4)) (p : Equiv.Perm (Fin 2)) :
    H.merge (H.merge (positive c) e) p Fin.elim0=(count e p : ℂ)*c := by
  change (positive c (assignment e p false false)+positive c (assignment e p true false))+
    (positive c (assignment e p false true)+positive c (assignment e p true true))=_
  simp only [count,Fintype.sum_bool,Nat.cast_add]
  simp only [positive,EOBinaryPlaneCore.lift]
  change (if compatible (assignment e p false false) then c else 0)+
    (if compatible (assignment e p true false) then c else 0)+
    ((if compatible (assignment e p false true) then c else 0)+
      (if compatible (assignment e p true true) then c else 0))=_
  split_ifs <;> norm_num <;> ring

theorem closed_value (c : ℂ) (e : Equiv.Perm (Fin 4)) (p : Equiv.Perm (Fin 2)) :
    H.merge (H.merge (positive c) e) p Fin.elim0=2*c ∨
      H.merge (H.merge (positive c) e) p Fin.elim0=4*c := by
  rw [closed_factor]
  rcases count_two_or_four e p with h|h
  · left; rw [h]; norm_num
  · right; rw [h]; norm_num

/-- The two closures may use any original port orders at both stages. -/
theorem native_closure_value (S : Network ℂ 4) (c : ℂ) (hS : S.denote=positive c)
    {Q : Network ℂ 0} (h : N.NativeClosure S Q) :
    Q.denote Fin.elim0=2*c ∨ Q.denote Fin.elim0=4*c := by
  cases h with
  | step S e tail =>
    cases tail with
    | step U p tail =>
      cases tail with
      | done Q =>
        rw [H.merge_denote,H.merge_denote,hS]
        exact closed_value c e p

/-- The residual's own coordinate permutation can be absorbed into either
closure order. Its physical graph is never replaced by a free row. -/
theorem permuted_native_closure_value (S : Network ℂ 4) (c : ℂ)
    (r : Equiv.Perm (Fin 4)) (hS : Tensor.reindex r S.denote=positive c)
    {Q : Network ℂ 0} (h : N.NativeClosure S Q) :
    Q.denote Fin.elim0=2*c ∨ Q.denote Fin.elim0=4*c := by
  have hr : S.denote=Tensor.reindex r.symm (positive c) := by
    funext x
    have hx := congrFun hS (x ∘ r.symm)
    change S.denote ((x ∘ r.symm) ∘ r)=positive c (x ∘ r.symm) at hx
    simpa [Function.comp_def] using hx
  cases h with
  | step S e tail =>
    cases tail with
    | step U p tail =>
      cases tail with
      | done Q =>
        rw [H.merge_denote,H.merge_denote,hr]
        change H.merge (H.merge (positive c) (r.symm.trans e)) p Fin.elim0=2*c ∨
          H.merge (H.merge (positive c) (r.symm.trans e)) p Fin.elim0=4*c
        exact closed_value c (r.symm.trans e) p

theorem native_closure_zero (S : Network ℂ 4) (hS : S.denote=0)
    {Q : Network ℂ 0} (h : N.NativeClosure S Q) : Q.denote Fin.elim0=0 := by
  obtain ⟨e,he⟩ := GeneralEOPhaseExtractionMatchingNormalForm.normal_form 2 S h
  rw [he,hS]
  simp [GeneralEOPhaseExtractionMatchingNormalForm.value,
    GeneralEOPhaseExtractionLoopTomography.merge,Tensor.reindex]

/-- The exact local switch rule includes simultaneous vanishing, which is
needed to propagate a common phase through a connected matching graph. -/
theorem comparison (S : Network ℂ 4)
    (hS : S.denote=0 ∨ ∃c : ℂ,∃r : Equiv.Perm (Fin 4),Tensor.reindex r S.denote=positive c)
    {P Q : Network ℂ 0} (hP : N.NativeClosure S P) (hQ : N.NativeClosure S Q) :
    (P.denote Fin.elim0=0 ↔ Q.denote Fin.elim0=0) ∧
      GeneralEOPhaseExtractionCore.Collinear (P.denote Fin.elim0) (Q.denote Fin.elim0) := by
  rcases hS with hz|⟨c,r,hr⟩
  · rw [native_closure_zero S hz hP,native_closure_zero S hz hQ]
    exact ⟨Iff.rfl,GeneralEOPhaseExtractionCore.collinear_zero_left 0⟩
  · rcases permuted_native_closure_value S c r hr hP with hp|hp <;>
      rcases permuted_native_closure_value S c r hr hQ with hq|hq
    all_goals
      rw [hp,hq]
      constructor
      · norm_num [mul_eq_zero]
      · simp [GeneralEOPhaseExtractionCore.Collinear,GeneralEOPhaseExtractionCore.area,
          Complex.mul_re,Complex.mul_im]
        all_goals ring

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseExtractionPositiveSwitch
