import Holant.Proofs.Hardness.GeneralCancellationCapPin
import Holant.Proofs.Hardness.DenseTwoCoefficientEscape
import Holant.Complexity.BinaryInterpolation.AlgebraicSource.Macro

/-! Actual ordered cap powers. The norm condition below is a literal coefficient
condition; infinite order and the directed-pinning pencil are derived internally.
This local module does not claim a completed interpolation programme. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralGeometricCapLocal
open Holant Holant.Complexity.BinaryInterpolation
open Holant.Certificates.MatchingContractionClosure
open Holant.Projective.BoundedTorsion
namespace Cap
export GeneralCancellationCapPin (Choice network oriented full_table)
end Cap
variable {K : Type*} [Field K]

def anti (p q : K) : Binary (K:=K) := fun a b =>
  if a then (if b then 0 else q) else (if b then p else 0)

theorem transfer (p q : K) : anti p q * X=Matrix.diagonal (fun a : Bool=>if a then q else p) := by
  ext a b
  cases a <;> cases b <;> simp [anti,X,Matrix.mul_apply,Signature.disequality]

theorem power (p q : K) (n : ℕ) : (anti p q*X)^n*X=anti (p^n) (q^n) := by
  rw [transfer,Matrix.diagonal_pow]
  ext a b
  cases a <;> cases b <;> simp [anti,X,Matrix.mul_apply,Signature.disequality]

theorem normalized (p q : K) (hq : q≠0) (n : ℕ) :
    (anti p q*X)^n*X=q^n • (anti 0 1+(p/q)^n • anti 1 0) := by
  rw [power]
  ext a b
  cases a <;> cases b <;>
    simp [anti,Matrix.smul_apply,smul_eq_mul,div_eq_mul_inv,mul_pow,
      mul_left_comm,pow_ne_zero n hq]

theorem actual_cap (M : Signature K 4)
    (hM : Holant.LocalDrafts.Hardness.EightVertexNonexception.EvenSupport M) (k : Cap.Choice) :
    (Cap.network M k).denote=Chains.binarySignature (anti (Cap.oriented M k).1 (Cap.oriented M k).2) :=
  Cap.full_table M hM k

theorem actual_chain (M : Signature K 4)
    (hM : Holant.LocalDrafts.Hardness.EightVertexNonexception.EvenSupport M)
    (k : Cap.Choice) (n : ℕ) :
    (Chains.copies (Cap.network M k) n).denote=
      Chains.binarySignature (anti ((Cap.oriented M k).1^(n+1)) ((Cap.oriented M k).2^(n+1))) := by
  rw [Chains.copies_denote _ _ (actual_cap M hM k),power]

theorem infinite_transfer (p q : K) (_hq : q≠0)
    (hi : ∀ n : ℕ,0<n → (p/q)^n≠1) : ¬ProjectivelyFinite (anti p q*X) := by
  rintro ⟨n,hn,c,hc,he⟩
  have hp := congrArg (fun A : Binary (K:=K)=>A false false) he
  have hq' := congrArg (fun A : Binary (K:=K)=>A true true) he
  rw [transfer,Matrix.diagonal_pow] at hp hq'
  simp at hp hq'
  apply hi n hn
  rw [div_pow,hp,hq',div_self hc]

/-- No supplied spectral certificate: unequal literal norms force infinite ratio. -/
theorem infinite_of_unequal_norms {L : Type*} [NormedField L]
    (p q : L) (hq : q≠0) (h : ‖p‖≠‖q‖) :
    ∀ n : ℕ,0<n → (p/q)^n≠1 := by
  intro n hn he
  have hnorm : ‖p/q‖^n=1 := by simpa only [norm_pow,norm_one] using congrArg norm he
  have hone := (pow_eq_one_iff_of_nonneg (norm_nonneg (p/q)) (Nat.ne_of_gt hn)).mp hnorm
  rw [norm_div] at hone
  exact h ((div_eq_one_iff_eq (norm_ne_zero_iff.mpr hq)).mp hone)

def Applicable {L : Type*} [NormedField L] (M : Signature L 4) : Prop :=
  ∃ k : Cap.Choice, (Cap.oriented M k).1≠0 ∧ (Cap.oriented M k).2≠0 ∧
    ‖(Cap.oriented M k).1‖≠‖(Cap.oriented M k).2‖

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralGeometricCapLocal
