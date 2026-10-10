import Holant.Pauli.ExoticKlein.MatchingCardCalculus
import Holant.Certificates.MatchingContractionClosure.CollectionClosure
import Holant.Pauli.ExoticKlein.Matching

/-! The exotic four-line family is an actual saturated matrix group, with
native-X reversal and transfer handled explicitly. Thus the shared arbitrary
matching-contraction theorem applies to literal exotic matching tensors. -/
namespace Holant.Pauli.ExoticKlein
noncomputable section
open scoped BigOperators
namespace MatchingCard
open Holant.Certificates.MatchingContractionClosure

def binaryGroup : Set (Binary (K := ℂ)) :=
  {A | ∃ a : Label, ∃ c : ℂ, c ≠ 0 ∧ A = c • asMatrix (E a)}

theorem E_mem (a : Label) : asMatrix (E a) ∈ binaryGroup :=
  ⟨a,1,one_ne_zero,(one_smul _ _).symm⟩

theorem group_mul {A B : Binary (K := ℂ)} (hA : A ∈ binaryGroup) (hB : B ∈ binaryGroup) :
    A*B ∈ binaryGroup := by
  obtain ⟨a,s,hs,rfl⟩ := hA
  obtain ⟨b,t,ht,rfl⟩ := hB
  refine ⟨a+b,s*t*omega a b,mul_ne_zero (mul_ne_zero hs ht) (omega_ne_zero a b),?_⟩
  rw [Matrix.smul_mul,Matrix.mul_smul,smul_smul,asMatrix_mul,fusion,asMatrix_scale,smul_smul]

theorem group_scale {A : Binary (K := ℂ)} (hA : A ∈ binaryGroup) (c : ℂ) (hc : c ≠ 0) :
    c • A ∈ binaryGroup := by
  obtain ⟨a,s,hs,rfl⟩ := hA
  exact ⟨a,c*s,mul_ne_zero hc hs,smul_smul c s _⟩

theorem group_inverse {A : Binary (K := ℂ)} (hA : A ∈ binaryGroup) :
    ∃ B ∈ binaryGroup, A*B=1 ∧ B*A=1 := by
  obtain ⟨a,s,hs,rfl⟩ := hA
  let t := (s*omega a a)⁻¹
  have ht : t ≠ 0 := inv_ne_zero (mul_ne_zero hs (omega_ne_zero a a))
  refine ⟨t • asMatrix (E a),⟨a,t,ht,rfl⟩,?_,?_⟩
  · rw [Matrix.smul_mul,Matrix.mul_smul,E_square,smul_smul,smul_smul]
    have hc : s*t*omega a a = 1 := by dsimp [t]; field_simp [hs,omega_ne_zero a a]
    rw [hc,one_smul]
  · rw [Matrix.smul_mul,Matrix.mul_smul,E_square,smul_smul,smul_smul]
    have hc : t*s*omega a a = 1 := by
      rw [mul_assoc]
      exact inv_mul_cancel₀ (mul_ne_zero hs (omega_ne_zero a a))
    rw [hc,one_smul]

theorem binaryGroup_projective : ProjectiveMatrixGroup binaryGroup where
  one_mem := by simpa only [asMatrix_zero] using E_mem 0
  mul_mem _ hA _ hB := group_mul hA hB
  inverse_mem _ hA := group_inverse hA
  scalar_mem _ hA c hc := group_scale hA c hc

theorem asMatrix_transpose (A : Mat) : (asMatrix A).transpose = asMatrix (Kernel.transpose A) := rfl

theorem group_transpose {A : Binary (K := ℂ)} (hA : A ∈ binaryGroup) : A.transpose ∈ binaryGroup := by
  obtain ⟨a,s,hs,rfl⟩ := hA
  refine ⟨theta a,s*transposeScalar a,mul_ne_zero hs (transposeScalar_ne_zero a),?_⟩
  rw [Matrix.transpose_smul,asMatrix_transpose,transpose_E,asMatrix_scale,smul_smul]

theorem asMatrix_X : asMatrix (E xLabel) = (X : Binary (K := ℂ)) := by
  ext u v
  cases u <;> cases v <;> rfl

theorem X_mem : (X : Binary (K := ℂ)) ∈ binaryGroup := by
  rw [←asMatrix_X]
  exact E_mem xLabel

theorem binaryGroup_reversal : ReversalStable binaryGroup := by
  intro A hA
  exact group_mul (group_mul X_mem (group_transpose hA)) X_mem

theorem safe_iff_mem (A : Binary (K := ℂ)) : SafeBinary binaryGroup A ↔ A ∈ binaryGroup := by
  constructor
  · intro hA
    have hh := group_mul hA X_mem
    simpa only [transfer,Matrix.mul_assoc,X_mul_X,Matrix.mul_one] using hh
  · intro hA
    exact group_mul hA X_mem

theorem E_safe (a : Label) : SafeBinary binaryGroup (asMatrix (E a)) :=
  (safe_iff_mem _).mpr (E_mem a)

theorem dual_mem (a : Label) : asMatrix (dual a) ∈ binaryGroup := by
  refine ⟨theta a,(d a)⁻¹,inv_ne_zero (d_ne_zero a),?_⟩
  ext u v
  rfl

theorem dual_safe (a : Label) : SafeBinary binaryGroup (asMatrix (dual a)) :=
  (safe_iff_mem _).mpr (dual_mem a)

/-- A scalar multiple of an actual exotic matching tensor, with arbitrary
matching size and original physical port type. -/
def ExoticMatchingOrZero {P : Type*} (h : Tensor ℂ P) : Prop :=
  h = 0 ∨ ∃ r, ∃ M : Matching P r, ∃ labels : Fin r → Label, ∃ s : ℂ,
    s ≠ 0 ∧ h = fun x => s*M.tensor labels x

theorem exotic_iff_group {P : Type*} (h : Tensor ℂ P) :
    ExoticMatchingOrZero h ↔ MatchingOrZero binaryGroup h := by
  constructor
  · rintro (hz | ⟨r,M,labels,s,hs,he⟩)
    · exact Or.inl hz
    · refine Or.inr ⟨⟨r,M.ports,fun e => asMatrix (E (labels e)),s⟩,fun e => E_safe _,hs,?_⟩
      exact he
  · rintro (hz | ⟨M,hM,hs,he⟩)
    · exact Or.inl hz
    · have hm : ∀ e, ∃ a : Label, ∃ c : ℂ, c ≠ 0 ∧ M.matrix e = c • asMatrix (E a) :=
        fun e => (safe_iff_mem _).mp (hM e)
      choose labels scalars hscalars hmatrix using hm
      refine Or.inr ⟨M.edges,⟨M.ports⟩,labels,M.scalar*∏ e, scalars e,
        mul_ne_zero hs (Finset.prod_ne_zero_iff.mpr (fun e he => hscalars e)),?_⟩
      rw [he]
      funext x
      simp only [Presentation.tensor,productValue,hmatrix,Matrix.smul_apply,smul_eq_mul,
        asMatrix,Matrix.of_apply,Finset.prod_mul_distrib,Matching.tensor,mul_assoc]

/-- Arbitrary actual disjoint collections preserve exotic matching products,
including every zero cycle trace and the nullary boundary. -/
theorem exotic_collection_closed {P Q J : Type*} [DecidableEq P] [Fintype J] [DecidableEq J]
    (ports : CollectionPorts P Q J) (kernels : J → Label) (h : Tensor ℂ P)
    (hs : ExoticMatchingOrZero h) :
    ExoticMatchingOrZero (contractCollection ports (fun e => asMatrix (dual (kernels e))) h) := by
  apply (exotic_iff_group _).mpr
  exact contractCollection_closed binaryGroup_projective X_mem binaryGroup_reversal ports
    (fun e => asMatrix (dual (kernels e))) h (fun e => dual_safe _) ((exotic_iff_group _).mp hs)

end MatchingCard
end
end Holant.Pauli.ExoticKlein
