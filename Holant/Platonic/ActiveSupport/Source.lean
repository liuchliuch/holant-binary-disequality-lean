import Holant.Platonic.ActiveSupport.CommonNormalization
import Holant.Platonic.ActiveSupport.IncidenceSpan
import Holant.Certificates.TetrahedralAffine.Binaries

/-! Source Lemma 9.19: the actual tetrahedral card cube has at most four active
qubits. The one common analytic Clifford is constructed from a nonzero actual
test image. Its amplitude is retained, as required by amendment M002. -/
namespace Holant.Platonic.ActiveSupport
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open Holant.Platonic.StabilizerLine Holant.Certificates.MatchingProductBridge
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

theorem normalized_span_le_four (Φ : Binary →ₗ[ℂ] Signature ℂ n)
    (hΦ : TetrahedralAffine Φ) (α : ℂ) (hα : α≠0)
    (hA : Φ anchor=fun x => α*delta x) :
    Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2) (pairedSupportUnion Φ : Set (BinaryVector n)))≤4 := by
  apply four_support_span_le_four (pairedSupports Φ)
  · exact fun j => (pairedSupports_shape Φ hΦ α hα hA j).1
  · exact fun j => (pairedSupports_shape Φ hΦ α hα hA j).2
  · exact pairedSupports_double Φ α hA

/-- Full source conclusion, with no assumed normalization, spanning, transport,
incidence, or support witness. Every complex input matrix is covered. -/
theorem source_four_active_qubits (Φ : Binary →ₗ[ℂ] Signature ℂ n)
    (htest : ∀K,tetrahedralBase K → Φ K=0 ∨ ComplexAffine (Φ K)) :
    ∃ (C : AnalyticClifford n) (R : BinaryCode n),Module.finrank (ZMod 2) R≤4 ∧
      ∀ (K : Binary) (x : BinaryVector n),C.operator (Φ K) (wordVector x)≠0 → x∈R := by
  by_cases hz : Φ=0
  · refine ⟨Program.identity.clifford,⊥,by simp,?_⟩
    intro K x hx
    simp [hz] at hx
  have hΦ : TetrahedralAffine Φ := by
    intro K hK
    rcases htest K hK with he|ha
    · rw [he]
      exact ⟨0,0,affine_zero n,by simp⟩
    · exact ha
  obtain ⟨L,hL,hLs,hLne⟩ := exists_tetrahedral_transport Φ hz
  let Ψ := Φ.comp (leftMultiply L)
  have hΨ : TetrahedralAffine Ψ := hΦ.transport L hL
  obtain ⟨C,α,hα,hA,hC,_⟩ := exists_clifford_normalization (Ψ anchor)
    (hΨ anchor anchor_base) hLne
  let Θ := C.operator.toLinearMap.comp Ψ
  have hΘ : TetrahedralAffine Θ := hΨ.clifford C hC
  refine ⟨C,Submodule.span (ZMod 2) (pairedSupportUnion Θ : Set (BinaryVector n)),
    normalized_span_le_four Θ hΘ α hα hA,?_⟩
  intro K x hx
  obtain ⟨J,hJ⟩ := hLs K
  apply support_all_matrices Θ J x
  change C.operator (Φ (leftMultiply L J)) (wordVector x)≠0
  rwa [hJ]

/-- Exactly the twelve existing literal quaternion representatives. -/
theorem source_twelve_four_active_qubits (Φ : Binary →ₗ[ℂ] Signature ℂ n)
    (htest : ∀r : Holant.Certificates.TetrahedralAffine.Representative,
      Φ (Holant.Certificates.TetrahedralAffine.complexKernel r)=0 ∨
        ComplexAffine (Φ (Holant.Certificates.TetrahedralAffine.complexKernel r))) :
    ∃ (C : AnalyticClifford n) (R : BinaryCode n),Module.finrank (ZMod 2) R≤4 ∧
      ∀ (K : Binary) (x : BinaryVector n),C.operator (Φ K) (wordVector x)≠0 → x∈R := by
  apply source_four_active_qubits Φ
  intro K hK
  obtain ⟨r,rfl⟩ := Holant.Certificates.TetrahedralAffine.base_covered hK
  exact htest r

/-- Literal finite binary equations and even-mixed fourth-root phase formulas,
with arbitrary nonzero complex exterior amplitudes, suffice for all twelve tests. -/
theorem source_literal_four_active_qubits (Φ : Binary →ₗ[ℂ] Signature ℂ n)
    (htest : ∀K,tetrahedralBase K → Φ K=0 ∨
      ∃c : ℂ,c≠0 ∧ ∃S : AffineSystem n,∃Q : QuadraticPhase n,
        Φ K=complexAffineFormula c S Q) :
    ∃ (C : AnalyticClifford n) (R : BinaryCode n),Module.finrank (ZMod 2) R≤4 ∧
      ∀ (K : Binary) (x : BinaryVector n),C.operator (Φ K) (wordVector x)≠0 → x∈R := by
  apply source_four_active_qubits Φ
  intro K hK
  exact Or.inr ((complexAffine_iff_literal (Φ K)).mpr (htest K hK))

/-- Projective representatives may have any specified nonzero scales. -/
theorem source_projective_four_active_qubits (D : Set Binary)
    (Φ : Binary →ₗ[ℂ] Signature ℂ n)
    (hcontains : ∀K,tetrahedralBase K → ∃c : ℂ,c≠0 ∧ c • K∈D)
    (htest : ∀K∈D,Φ K=0 ∨ ComplexAffine (Φ K)) :
    ∃ (C : AnalyticClifford n) (R : BinaryCode n),Module.finrank (ZMod 2) R≤4 ∧
      ∀ (K : Binary) (x : BinaryVector n),C.operator (Φ K) (wordVector x)≠0 → x∈R := by
  apply source_four_active_qubits Φ
  intro K hK
  obtain ⟨c,hc,hd⟩ := hcontains K hK
  have hh := htest (c • K) hd
  rw [map_smul] at hh
  rcases hh with hz|ha
  · left
    exact (smul_eq_zero.mp hz).resolve_left hc
  · right
    have hs := ha.scale c⁻¹
    convert hs using 1
    funext x
    change Φ K x=c⁻¹*(c*Φ K x)
    rw [←mul_assoc,inv_mul_cancel₀ hc,one_mul]

/-- The same conclusion in the signature's original Boolean word coordinates. -/
theorem source_support_subset (Φ : Binary →ₗ[ℂ] Signature ℂ n)
    (htest : ∀K,tetrahedralBase K → Φ K=0 ∨ ComplexAffine (Φ K)) :
    ∃ (C : AnalyticClifford n) (R : BinaryCode n),Module.finrank (ZMod 2) R≤4 ∧
      ∀K,Function.support (C.operator (Φ K))⊆{w | vectorWord w∈R} := by
  obtain ⟨C,R,hR,hs⟩ := source_four_active_qubits Φ htest
  refine ⟨C,R,hR,?_⟩
  intro K w hw
  exact hs K (vectorWord w) (by simpa using hw)

end
end Holant.Platonic.ActiveSupport
