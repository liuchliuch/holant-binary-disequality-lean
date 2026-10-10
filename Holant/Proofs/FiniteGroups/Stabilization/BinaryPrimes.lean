import Holant.Proofs.FiniteGroups.Stabilization.FactorWorklist
import Holant.Proofs.FiniteGroups.Stabilization.Representatives
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic


namespace Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
noncomputable section
variable {L : Type*} [Field L]

theorem binary_det_formula (B : Binary (K := L)) :
    Matrix.det B = B false false * B true true - B false true * B true false := by
  rw [← Matrix.det_reindex_self finTwoEquiv.symm B, Matrix.det_fin_two]
  rfl

theorem singular_binary_split (B : Binary (K := L)) (hn : B ≠ 0) (hd : Matrix.det B = 0) :
    ∃ u v : Bool → L, ∀ a b, B a b = u a * v b := by
  classical
  have hp : ∃ i j, B i j ≠ 0 := by
    by_contra! h
    exact hn (by ext i j; exact h i j)
  obtain ⟨i₀, j₀, hp⟩ := hp
  have hdet : B false false * B true true = B false true * B true false := by
    exact sub_eq_zero.mp ((binary_det_formula B).symm.trans hd)
  have hc : ∀ i j, B i j * B i₀ j₀ = B i j₀ * B i₀ j := by
    intro i j
    cases i₀ <;> cases j₀ <;> cases i <;> cases j
    all_goals first | ring | simpa [mul_comm] using hdet | simpa [mul_comm] using hdet.symm
  refine ⟨fun i => B i j₀ / B i₀ j₀, fun j => B i₀ j, ?_⟩
  intro i j
  rw [div_mul_eq_mul_div]
  exact (eq_div_iff hp).mpr (hc i j)

theorem prime_binary_nonsingular (B : Binary (K := L))
    (hp : Prime (⟨2, binarySignature B⟩ : AnySignature L)) : Matrix.det B ≠ 0 := by
  intro hd
  have hn : B ≠ 0 := by
    intro hz
    apply hp.1
    funext x
    simp [binarySignature, hz]
  obtain ⟨u, v, huv⟩ := singular_binary_split B hn hd
  let a : AnySignature L := ⟨1, fun x => u (x 0)⟩
  let b : AnySignature L := ⟨1, fun x => v (x 0)⟩
  apply hp.2
  refine ⟨a, b, ⟨{
    left_pos := (by change 0 < 1; decide), right_pos := (by change 0 < 1; decide),
    ports := finSumFinEquiv, scale := 1, equation := ?_ }⟩⟩
  funext x
  change B (x 0) (x 1) = 1 * (u (x 0) * v (x 1))
  rw [one_mul]
  exact huv (x 0) (x 1)

def binaryMatrix (f : Signature L 2) : Binary (K := L) := fun a b => f ![a,b]

@[simp] theorem binarySignature_binaryMatrix (f : Signature L 2) :
    binarySignature (binaryMatrix f) = f := by
  funext x
  have hx : ![x 0,x 1] = x := by funext i; fin_cases i <;> rfl
  exact congrArg f hx

theorem retained_binary_prime_actual (F : SignatureFamily L) (f : Signature L 2)
    (hf : (⟨2, f⟩ : AnySignature L) ∈ F) (hp : Prime (⟨2, f⟩ : AnySignature L)) :
    ActualNonsingular F (binaryMatrix f) := by
  refine ⟨?_, ?_⟩
  · rw [binarySignature_binaryMatrix]
    exact Gadget.realizes_of_mem F .disequality f hf
  · apply prime_binary_nonsingular
    simpa only [binarySignature_binaryMatrix] using hp

theorem retained_binary_prime_safe (F : SignatureFamily L) (f : Signature L 2)
    (hf : (⟨2, f⟩ : AnySignature L) ∈ F) (hp : Prime (⟨2, f⟩ : AnySignature L)) :
    SafeBinary (actualTransfers F) (binaryMatrix f) :=
  ⟨binaryMatrix f, retained_binary_prime_actual F f hf hp, 1, one_ne_zero, (one_smul L _).symm⟩

/-- Recover the exact scalar multiplying a frozen actual representative. -/
theorem actual_binary_eq_representative (F : SignatureFamily L) (hτ : ResidualTorsion F)
    (B : Binary (K := L)) (hB : ActualNonsingular F B) :
    ∃ q : completeGroup F hτ, ∃ c : L, c ≠ 0 ∧ B = c • actualRepresentative F hτ q := by
  obtain ⟨q, hq⟩ := actualRepresentative_covers F hτ hB
  obtain ⟨c, hc, he⟩ := projectiveClass_eq_iff.mp hq.symm
  refine ⟨q, c, hc, ?_⟩
  have hh := congrArg (fun M : Binary (K := L) => M * X) he
  simpa only [transfer, Matrix.smul_mul, Matrix.mul_assoc, X_mul_X, Matrix.mul_one] using hh

end
end Holant.LocalDrafts.FinitePGL2.Stabilization
