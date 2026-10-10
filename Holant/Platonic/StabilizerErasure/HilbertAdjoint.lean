import Holant.Platonic.StabilizerErasure.NonzeroColumns

/-! The actual finite-dimensional Hermitian adjoint of an arbitrary linear
map, and the exact source KL predicate without an encoder presentation. -/
namespace Holant.Platonic.StabilizerErasure
open Holant Holant.Tractable.AffinePhase Holant.Platonic.StabilizerLine
open scoped BigOperators ComplexConjugate
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n k : ℕ}

def hilbertAdjoint (U : Signature ℂ k →ₗ[ℂ] Signature ℂ n) :
    Signature ℂ n →ₗ[ℂ] Signature ℂ k where
  toFun g x := ∑y,conj (U (ket x) y)*g y
  map_add' g h := by ext x;simp [mul_add,Finset.sum_add_distrib]
  map_smul' c g := by ext x;simp [Finset.mul_sum,mul_left_comm]

theorem hermitian_hilbertAdjoint (U : Signature ℂ k →ₗ[ℂ] Signature ℂ n)
    (f : Signature ℂ k) (g : Signature ℂ n) :
    hermitian (U f) g=hermitian f (hilbertAdjoint U g) := by
  have hv (y : Word n) : U f y=∑x : Word k,f x*U (ket x) y := by
    have he := congrFun (congrArg U (ket_expansion f)) y
    simpa only [map_sum,map_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul] using he
  unfold hermitian
  simp_rw [hv,map_sum,map_mul,Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [hilbertAdjoint,LinearMap.coe_mk,AddHom.coe_mk,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring

theorem hilbertAdjoint_encoder (V : StabilizerIsometry k n) :
    hilbertAdjoint V.map=V.adjoint := by
  apply LinearMap.ext
  intro g
  apply hermitian_ext
  intro f
  rw [←hermitian_hilbertAdjoint,←V.adjoint_identity]

def CorrectableMap (U : Signature ℂ k →ₗ[ℂ] Signature ℂ (n+1)) (r : Fin (n+1)) : Prop :=
  ∀R : Kernel ℂ,IsScalar (fun f => hilbertAdjoint U (siteAction r R (U f)))

theorem correctableMap_encoder (V : StabilizerIsometry k (n+1)) (r : Fin (n+1)) :
    CorrectableMap V.map r ↔ Correctable V r := by
  simp only [CorrectableMap,Correctable,hilbertAdjoint_encoder]

theorem correctableMap_iff_hermitian
    (U : Signature ℂ k →ₗ[ℂ] Signature ℂ (n+1)) (r : Fin (n+1)) :
    CorrectableMap U r ↔ ∀R : Kernel ℂ,∃c : ℂ,∀f g,
      hermitian (U f) (siteAction r R (U g))=c*hermitian f g := by
  constructor
  · intro h R
    obtain ⟨c,hc⟩ := h R
    change ∀f,hilbertAdjoint U (siteAction r R (U f))=c • f at hc
    refine ⟨c,?_⟩
    intro f g
    rw [hermitian_hilbertAdjoint,hc]
    simp [hermitian,Finset.mul_sum,mul_left_comm]
  · intro h R
    obtain ⟨c,hc⟩ := h R
    refine ⟨c,?_⟩
    intro g
    apply hermitian_ext
    intro f
    rw [←hermitian_hilbertAdjoint,hc]
    simp [hermitian,Finset.mul_sum,mul_left_comm]

theorem correctableMap_precompose
    (U : Signature ℂ k →ₗ[ℂ] Signature ℂ (n+1)) (L : AnalyticClifford k) (r : Fin (n+1)) :
    CorrectableMap (U.comp L.operator.toLinearMap) r ↔ CorrectableMap U r := by
  rw [correctableMap_iff_hermitian,correctableMap_iff_hermitian]
  constructor
  · intro h R
    obtain ⟨c,hc⟩ := h R
    refine ⟨c,?_⟩
    intro f g
    have he := hc (L.operator.symm f) (L.operator.symm g)
    have hi : hermitian (L.operator.symm f) (L.operator.symm g)=hermitian f g := by
      simpa using (L.unitary (L.operator.symm f) (L.operator.symm g)).symm
    simpa [hi] using he
  · intro h R
    obtain ⟨c,hc⟩ := h R
    refine ⟨c,?_⟩
    intro f g
    change hermitian (U (L.operator f)) (siteAction r R (U (L.operator g)))=c*hermitian f g
    rw [hc,L.unitary]

end
end Holant.Platonic.StabilizerErasure
