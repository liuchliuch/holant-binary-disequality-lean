import Holant.Platonic.StabilizerErasure.TensorAuxiliary
import Holant.Platonic.StabilizerErasure.ErasureNormalForms

/-! Transfer the actual residual stabilizer isometries through a logical
Clifford, including its identity extension on the mixed auxiliary qubit. -/
namespace Holant.Platonic.StabilizerErasure
open Holant Holant.Tractable.AffinePhase Holant.Platonic.StabilizerLine
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n k j : ℕ}

theorem clifford_semantic (C : AnalyticClifford n) : IsStabilizerIsometry C.operator.toLinearMap := by
  refine ⟨C.unitary,⟨0,Fin.elim0,?_,?_⟩,?_⟩
  · intro i;exact Fin.elim0 i
  · intro f
    constructor
    · intro _ i;exact Fin.elim0 i
    · intro _;exact ⟨C.operator.symm f,C.operator.apply_symm_apply f⟩
  · intro P
    obtain ⟨Q,hQ⟩ := C.pauli_forward P
    exact ⟨Q,fun f => (hQ f).symm⟩

theorem semantic_comp_surjective
    (U : Signature ℂ k →ₗ[ℂ] Signature ℂ n) (T : Signature ℂ j →ₗ[ℂ] Signature ℂ k)
    (hU : IsStabilizerIsometry U) (hT : IsStabilizerIsometry T) (hs : Function.Surjective T) :
    IsStabilizerIsometry (U.comp T) := by
  obtain ⟨hi,⟨t,P,hcomm,hcode⟩,hl⟩ := hU
  have hr : LinearMap.range (U.comp T)=LinearMap.range U := by
    ext f
    constructor
    · rintro ⟨g,rfl⟩;exact ⟨T g,rfl⟩
    · rintro ⟨g,rfl⟩
      obtain ⟨f,hf⟩ := hs g
      exact ⟨f,by simp [hf]⟩
  refine ⟨?_,⟨t,P,hcomm,?_⟩,?_⟩
  · intro f g
    exact (hi (T f) (T g)).trans (hT.1 f g)
  · intro f
    rw [hr]
    exact hcode f
  · intro Q
    obtain ⟨R,hR⟩ := hT.2.2 Q
    obtain ⟨S,hS⟩ := hl R
    exact ⟨S,fun f => by change S.run (U (T f))=U (T (Q.run f));rw [hS,hR]⟩

theorem prependMap_surjective (T : Signature ℂ k →ₗ[ℂ] Signature ℂ n)
    (hs : Function.Surjective T) : Function.Surjective (prependMap T) := by
  intro f
  choose g hg using fun b : Bool => hs (column 0 b f)
  refine ⟨assembleColumns g,?_⟩
  apply columns_ext
  intro b
  simp [hg]

theorem prependMap_auxiliaryKet (T : Signature ℂ k →ₗ[ℂ] Signature ℂ n)
    (b : Bool) (f : Signature ℂ k) :
    prependMap T (auxiliaryKet b f)=auxiliaryKet b (T f) := by
  apply columns_ext
  intro c
  by_cases hc : c=b <;> simp [column_prependMap,column_auxiliaryKet,hc]

theorem pureForm_precompose (T : Signature ℂ k →ₗ[ℂ] Signature ℂ (n+1))
    (r : Fin (n+1)) (L : AnalyticClifford k) (h : PureStabilizerForm T r) :
    PureStabilizerForm (T.comp L.operator.toLinearMap) r := by
  obtain ⟨b,W,hW,he⟩ := h
  exact ⟨b,W.comp L.operator.toLinearMap,
    semantic_comp_surjective W _ hW (clifford_semantic L) L.operator.surjective,
    fun f w => he (L.operator f) w⟩

theorem mixedForm_precompose (T : Signature ℂ k →ₗ[ℂ] Signature ℂ (n+1))
    (r : Fin (n+1)) (L : AnalyticClifford k) (h : MixedStabilizerForm T r) :
    MixedStabilizerForm (T.comp L.operator.toLinearMap) r := by
  obtain ⟨W,hW,he⟩ := h
  refine ⟨W.comp (prependMap L.operator.toLinearMap),
    semantic_comp_surjective W _ hW (prependMap_stabilizer _ (clifford_semantic L))
      (prependMap_surjective _ L.operator.surjective),?_⟩
  intro f b w
  change T (L.operator f) (r.insertNth b w)=
    _*W (prependMap L.operator.toLinearMap (auxiliaryKet b f)) w
  rw [prependMap_auxiliaryKet]
  exact he (L.operator f) b w

end
end Holant.Platonic.StabilizerErasure
