import Holant.Kernel
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-! Actual matrix representatives for Lemma9.10. The hypotheses are precisely
a saturated projective matrix group, reversal stability and membership of X. -/
namespace Holant.Certificates.MatchingContractionClosure
open Holant
noncomputable section
variable {K : Type*} [Field K]

abbrev Binary := Matrix Bool Bool K

def X : Binary (K := K) := Matrix.of Signature.disequality

theorem X_mul_X : (X : Binary (K := K))*X=1 := by
  ext a b
  cases a <;> cases b <;> simp [X,Matrix.mul_apply,Matrix.one_apply,Signature.disequality]

theorem transpose_X : (X : Binary (K := K)).transpose=X := by
  ext a b
  cases a <;> cases b <;> rfl

structure ProjectiveMatrixGroup (G : Set (Binary (K := K))) : Prop where
  one_mem : (1 : Binary (K := K)) ∈ G
  mul_mem : ∀ U ∈ G, ∀ V ∈ G, U*V ∈ G
  inverse_mem : ∀ U ∈ G, ∃ V ∈ G, U*V=1 ∧ V*U=1
  scalar_mem : ∀ U ∈ G, ∀ c : K, c ≠ 0 → c • U ∈ G

theorem ProjectiveMatrixGroup.det_ne_zero {G : Set (Binary (K := K))}
    (hG : ProjectiveMatrixGroup G) {U : Binary (K := K)} (hU : U ∈ G) : Matrix.det U ≠ 0 := by
  obtain ⟨V,hV,hUV,hVU⟩ := hG.inverse_mem U hU
  have hd := congrArg Matrix.det hUV
  rw [Matrix.det_mul,Matrix.det_one] at hd
  intro hz
  simp [hz] at hd

def transfer (B : Binary (K := K)) : Binary (K := K) := B*X
def reverseTransfer (T : Binary (K := K)) : Binary (K := K) := X*T.transpose*X
def ReversalStable (G : Set (Binary (K := K))) : Prop := ∀ U ∈ G, reverseTransfer U ∈ G
def SafeBinary (G : Set (Binary (K := K))) (B : Binary (K := K)) : Prop := transfer B ∈ G

theorem transfer_transpose (B : Binary (K := K)) :
    transfer B.transpose=reverseTransfer (transfer B) := by
  simp only [transfer,reverseTransfer,Matrix.transpose_mul,transpose_X]
  rw [← Matrix.mul_assoc,X_mul_X,Matrix.one_mul]

theorem transfer_mul (U V : Binary (K := K)) :
    transfer (U*V)=transfer U*X*transfer V := by
  simp only [transfer]
  rw [Matrix.mul_assoc U X X,X_mul_X,Matrix.mul_one,Matrix.mul_assoc]

theorem SafeBinary.nonsingular {G : Set (Binary (K := K))} (hG : ProjectiveMatrixGroup G)
    {B : Binary (K := K)} (hB : SafeBinary G B) : Matrix.det B ≠ 0 := by
  have hd := hG.det_ne_zero hB
  unfold transfer at hd
  rw [Matrix.det_mul] at hd
  exact (mul_ne_zero_iff.mp hd).1

theorem SafeBinary.transpose {G : Set (Binary (K := K))} (hrev : ReversalStable G)
    {B : Binary (K := K)} (hB : SafeBinary G B) : SafeBinary G B.transpose := by
  unfold SafeBinary
  rw [transfer_transpose]
  exact hrev _ hB

theorem SafeBinary.mul {G : Set (Binary (K := K))} (hG : ProjectiveMatrixGroup G)
    (hX : (X : Binary (K := K)) ∈ G) {U V : Binary (K := K)} (hU : SafeBinary G U) (hV : SafeBinary G V) :
    SafeBinary G (U*V) := by
  unfold SafeBinary
  rw [transfer_mul]
  exact hG.mul_mem _ (hG.mul_mem _ hU _ hX) _ hV

theorem SafeBinary.scale {G : Set (Binary (K := K))} (hG : ProjectiveMatrixGroup G)
    {B : Binary (K := K)} (hB : SafeBinary G B) {c : K} (hc : c ≠ 0) : SafeBinary G (c • B) := by
  unfold SafeBinary transfer
  rw [Matrix.smul_mul]
  exact hG.scalar_mem _ hB c hc

theorem safe_I {G : Set (Binary (K := K))} (hX : (X : Binary (K := K)) ∈ G) : SafeBinary G 1 := by
  simpa [SafeBinary,transfer] using hX

theorem safe_X {G : Set (Binary (K := K))} (hG : ProjectiveMatrixGroup G) : SafeBinary G X := by
  simpa [SafeBinary,transfer,X_mul_X] using hG.one_mem

/-- The source's oriented path-splice identity, without a discarded scalar. -/
theorem splice_transfer (B₁ C B₂ : Binary (K := K)) :
    transfer (B₁.transpose*C*B₂)=
      reverseTransfer (transfer B₁)*X*transfer C*X*transfer B₂ := by
  rw [transfer_mul,transfer_mul,transfer_transpose]

theorem safe_splice {G : Set (Binary (K := K))} (hG : ProjectiveMatrixGroup G)
    (hX : (X : Binary (K := K)) ∈ G) (hrev : ReversalStable G)
    {B₁ C B₂ : Binary (K := K)} (h₁ : SafeBinary G B₁) (hC : SafeBinary G C) (h₂ : SafeBinary G B₂) :
    SafeBinary G (B₁.transpose*C*B₂) :=
  SafeBinary.mul hG hX (SafeBinary.mul hG hX (SafeBinary.transpose hrev h₁) hC) h₂

end
end Holant.Certificates.MatchingContractionClosure
