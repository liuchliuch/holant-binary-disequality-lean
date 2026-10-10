import Holant.Complexity.BinaryInterpolation.RepeatedRoot

/-! Derived nonzero rank-one output pencils for every nonsingular infinite-order
binary transfer. These are exact analytic identities for the original matrix;
actual query compilation and bit-time interpolation remain separate. -/
namespace Holant.Complexity.BinaryInterpolation
open Holant.Certificates.MatchingContractionClosure
open Holant.Projective.BoundedTorsion
noncomputable section
variable {K : Type*} [Field K] [CharZero K]
set_option backward.isDefEq.respectTransparency false

theorem right_X_nonzero (A : Binary (K := K)) (hA : A≠0) : A*X≠0 := by
  intro h
  have hh := congrArg (fun T : Binary (K := K) => T*X) h
  exact hA (by simpa only [Matrix.mul_assoc,X_mul_X,Matrix.mul_one,zero_mul] using hh)

theorem right_X_singular (A : Binary (K := K)) (hA : Matrix.det A=0) : Matrix.det (A*X)=0 := by
  rw [Matrix.det_mul,hA,zero_mul]

theorem distinct_pencil (A : Binary (K := K)) (a b : K) (hab : a≠b)
    (ha : a≠0) (hb : b≠0) (ht : Matrix.trace A=a+b) (hd : Matrix.det A=a*b)
    (hi : ¬ProjectivelyFinite A) :
    ∃H L : Binary (K := K),H≠0 ∧ H.rank=1 ∧
      (∀r : ℕ,0<r → (a/b)^r≠1) ∧
      ∀t : ℕ,A^t*X=b^t • (L+(a/b)^t • H) := by
  let P := spectralProjector A a b
  have hp : P≠0 := spectralProjector_nonzero A a b hab ht
  have hpd : Matrix.det P=0 := spectralProjector_determinant A a b ht hd
  refine ⟨P*X,(1-P)*X,right_X_nonzero P hp,
    singular_binary_rank _ (right_X_nonzero P hp) (right_X_singular P hpd),
    eigenratio_infinite A a b hab ha hb ht hd hi,?_⟩
  intro t
  rw [distinct_power A a b hab ht hd,add_mul,Matrix.smul_mul,Matrix.smul_mul]
  change a^t • (P*X)+b^t • ((1-P)*X)=b^t • ((1-P)*X+(a/b)^t • (P*X))
  rw [smul_add,smul_smul]
  have he : b^t*(a/b)^t=a^t := by
    rw [div_pow]
    field_simp
  rw [he]
  exact add_comm _ _

theorem repeated_pencil (A : Binary (K := K)) (a : K) (ha : a≠0)
    (ht : Matrix.trace A=a+a) (hd : Matrix.det A=a*a)
    (hi : ¬ProjectivelyFinite A) :
    ∃H : Binary (K := K),H≠0 ∧ H.rank=1 ∧
      ∀t : ℕ,A^t*X=a^t • (X+(t:K) • H) := by
  let N := nilpotentPart A a
  have hn : N≠0 := nilpotentPart_nonzero A a ha hi
  have hnd : Matrix.det N=0 := nilpotentPart_det A a ht hd
  have hx : N*X≠0 := right_X_nonzero N hn
  have hs : a⁻¹ • (N*X)≠0 := smul_ne_zero (inv_ne_zero ha) hx
  have hd' : Matrix.det (a⁻¹ • (N*X))=0 := by
    rw [Matrix.det_smul,right_X_singular N hnd,mul_zero]
  refine ⟨a⁻¹ • (N*X),hs,singular_binary_rank _ hs hd',?_⟩
  intro t
  rw [repeated_power A a ha ht hd,Matrix.smul_mul,add_mul,Matrix.one_mul,
    Matrix.smul_mul,Matrix.smul_mul]

/-- Both spectral alternatives are derived for the arbitrary original transfer.
No diagonalizing basis or repeated-root form is provided by the caller. -/
theorem infinite_transfer_pencil [IsAlgClosed K] (A : Binary (K := K))
    (hdet : Matrix.det A≠0) (hi : ¬ProjectivelyFinite A) :
    (∃a b : K, a≠0 ∧ b≠0 ∧ a≠b ∧
      ∃H L : Binary (K := K), H≠0 ∧ H.rank=1 ∧
        (∀r : ℕ,0<r → (a/b)^r≠1) ∧
        ∀t : ℕ,A^t*X=b^t • (L+(a/b)^t • H)) ∨
    (∃a : K,a≠0 ∧ ∃H : Binary (K := K),H≠0 ∧ H.rank=1 ∧
      ∀t : ℕ,A^t*X=a^t • (X+(t:K) • H)) := by
  obtain ⟨a,b,ht,hd,_haEig,_hbEig⟩ := exists_eigenpair A
  have ha : a≠0 := (mul_ne_zero_iff.mp (hd ▸ hdet)).1
  have hb : b≠0 := (mul_ne_zero_iff.mp (hd ▸ hdet)).2
  by_cases he : a=b
  · subst b
    exact Or.inr ⟨a,ha,repeated_pencil A a ha ht hd hi⟩
  · exact Or.inl ⟨a,b,ha,hb,he,distinct_pencil A a b he ha hb ht hd hi⟩

end
end Holant.Complexity.BinaryInterpolation
