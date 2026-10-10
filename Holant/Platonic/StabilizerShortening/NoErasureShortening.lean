import Holant.Platonic.StabilizerShortening.PairContraction
import Holant.Platonic.StabilizerShortening.PortExtension
import Holant.Platonic.StabilizerShortening.ColumnDeletion
import Holant.Platonic.StabilizerShortening.CliffordAffine

/-! Full source no-erasure shortening, retaining an actual original-port card. -/
namespace Holant.Platonic.StabilizerShortening
open Holant Holant.Tractable Holant.Tractable.AffinePhase Holant.Tractable.TwoTranslate
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.AffinePatching
open Holant.Platonic.StabilizerLine Holant.Platonic.StabilizerCode
open Holant.Platonic.StabilizerErasure
open Holant.Certificates.TetrahedralAffine
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {k m n : ℕ}

theorem affineMap_coordinates (p : Word k → Word m) (hp : IsAffineMap p)
    (j : Fin n → Fin m) : IsAffineMap (fun x i=>p x (j i)) := by
  intro x y
  ext i
  exact congrFun (hp x y) (j i)

theorem linear_ket_sampling (U : Signature ℂ k →ₗ[ℂ] Signature ℂ n)
    (p : Word k → Word n) (hp : Function.Injective p) (a : Word k → ℂ)
    (he : ∀z,U (ket z)=a z • ket (p z)) (f : Signature ℂ k) (z : Word k) :
    U f (p z)=a z*f z := by
  conv_lhs => rw [ket_expansion f]
  simp [he,ket,hp.eq_iff,mul_comm]

theorem tensorMap_linearEquiv_cancel (t : ℕ)
    (e : Signature ℂ k ≃ₗ[ℂ] Signature ℂ k) (f : Signature ℂ (k+t)) :
    tensorMap t e.symm.toLinearMap (tensorMap t e.toLinearMap f)=f := by
  change (tensorMap t e.symm.toLinearMap).comp (tensorMap t e.toLinearMap) f=f
  rw [←tensorMap_comp]
  have he : e.symm.toLinearMap.comp e.toLinearMap=LinearMap.id := by ext x; simp
  rw [he,tensorMap_id]
  rfl

theorem column_form_actual_shortening (t : ℕ)
    (U : Signature ℂ k →ₗ[ℂ] Signature ℂ (n+2))
    (a : Fin (n+2) → Fin 4) (c : BinaryVector (n+2))
    (M : Matrix (Fin k) (Fin (n+2)) (ZMod 2)) (a₀ : ℂ) (Q : QuadraticPhase k)
    (ha₀ : a₀≠0) (hrank : M.rank=k) (hroom : k+2≤n+2)
    (hcol : ∀z,Signature.coordinateAction (fun j=>axisMatrix (a j))
      (U (ket (wordVector z)))=
        (a₀*(fourthRootPhase (Q.eval (wordVector z)) : ℂ)) •
          ket (wordVector (c+M.transpose.mulVec z)))
    (f : Signature ℂ (k+t)) (hf : ¬ComplexAffine f) :
    HasNonaffineTetrahedralCard (tensorMap t U f) := by
  obtain ⟨r,s,hrs,hdelete⟩ := exists_two_deletable_columns M hrank hroom
  obtain ⟨p,hpr,hps⟩ := exists_twoPorts r s hrs
  let word : Word k → Word (n+2) := affineBoolean c M.transpose.mulVecLin
  let residual : Word k → Word n := fun z j=>word z (p (.inr j))
  have hw : IsAffineMap word := affineBoolean_isAffine c M.transpose.mulVecLin
  have hp : IsAffineMap residual := affineMap_coordinates word hw (fun j=>p (.inr j))
  have hi : Function.Injective residual := by
    intro z w he
    apply vector_injective
    apply hdelete (vectorWord z) (vectorWord w)
    intro j hjr hjs
    obtain ⟨i,rfl⟩ := p.surjective j
    cases i with
    | inl b => cases b <;> simp_all
    | inr i =>
      have hh := congrArg boolEquiv (congrFun he i)
      simp only [residual,word,affineBoolean,wordVector,Matrix.mulVecLin_apply,
        Pi.add_apply,Equiv.apply_symm_apply] at hh
      exact add_left_cancel hh
  let phase : Word k → ℂ := fun z=>a₀*(fourthRootPhase (Q.eval z) : ℂ)
  let omega : Word k → ℂ := fun z=>effectiveKernel (a r) (a s) (word z r) (word z s)
  let weight : Word k → ℂ := fun z=>phase z*omega z
  have hphase : ComplexAffine phase := ⟨a₀,_,affine_quadratic_phase Q,fun _=>rfl⟩
  have homega : ComplexAffine omega := by
    have h := affine_complex_precompose (effectiveKernel_affine (a r) (a s))
      (fun z i=>word z (![r,s] i)) (affineMap_coordinates word hw ![r,s])
    simpa [omega] using h
  have hweight : ComplexAffine weight := affine_complex_mul hphase homega
  have hweightnz (z : Word k) : weight z≠0 := by
    exact mul_ne_zero (mul_ne_zero ha₀ (by exact_mod_cast fourthRootPhase_ne_zero (Q.eval z)))
      (effectiveKernel_full_support (a r) (a s) (word z r) (word z s))
  let C := physicalAxisClifford (fun j=>a (p (.inr j)))
  let D := pairCard p (selectedKernel (a r) (a s))
  let R := C.operator.toLinearMap.comp (D.comp U)
  have hR (z : Word k) : R (ket z)=weight z • ket (residual z) := by
    have hh := hcol (vectorWord z)
    simp only [word_vector] at hh
    have hv : U (ket z)=phase z • Signature.coordinateAction (fun j=>inverseAxis (a j)) (ket (word z)) := by
      have hh' := congrArg (coordinateMap (fun j=>inverseAxis (a j))) hh
      change Signature.coordinateAction _ (Signature.coordinateAction _ _) = _ at hh'
      rw [inverseAxis_coordinate_cancel] at hh'
      simpa only [coordinateMap_apply,map_smul,phase,word,affineBoolean,Matrix.mulVecLin_apply] using hh'
    change C.operator (D (U (ket z)))=_
    rw [hv,map_smul,map_smul]
    rw [physicalAxisClifford_tensor]
    have hh := axis_pairCard_inverse_ket p a (word z)
    rw [hpr,hps] at hh
    rw [hh]
    simp only [smul_smul]
    rfl
  have hs := linear_ket_sampling R residual hi weight hR
  let g := tensorMap t R f
  have hg : g≠0 ∧ ¬ComplexAffine g := by
    apply nonaffine_of_affine_recovery f g (fun x=>weight (tailWord t x))
      (extendWordMap t residual) (extendWordMap_affine t residual hp)
    · intro x;exact hweightnz _
    · exact affine_complex_precompose (affine_complex_inverse hweight hweightnz)
        (tailWord t) (tailWord_affine t)
    · intro x;exact tensorMap_sampling t R residual weight hs f x
    · exact hf
  have hcard : ¬ComplexAffine (tensorMap t D (tensorMap t U f)) := by
    intro h
    have haff := (semantic_isometry_affine_iff (tensorMap t C.operator.toLinearMap)
      (tensorMap_stabilizer t _ (clifford_semantic C)) _).mpr h
    apply hg.2
    simpa only [g,R,tensorMap_comp,LinearMap.comp_apply] using haff
  apply actual_card_of_tensorMap t p (selectedRepresentative (a r) (a s)) (tensorMap t U f)
  exact ⟨fun hz=>hcard (hz ▸ affine_zero_complex),hcard⟩

theorem no_correctable_actual_shortening (t : ℕ)
    (U : Signature ℂ k →ₗ[ℂ] Signature ℂ n) (hU : IsStabilizerIsometry U)
    (hn : NoCorrectableMap U) (hroom : k+2≤n)
    (f : Signature ℂ (k+t)) (hf : ¬ComplexAffine f) :
    HasNonaffineTetrahedralCard (tensorMap t U f) := by
  obtain ⟨a,B,c,M,a₀,Q,ha₀,hrank,_,hcol⟩ := source_semantic_column_normal_form U hU hn
  cases n with
  | zero => omega
  | succ n =>
    cases n with
    | zero => omega
    | succ n =>
      let V := U.comp B.operator.symm.toLinearMap
      let g := tensorMap t B.operator.toLinearMap f
      have hg : ¬ComplexAffine g := by
        intro h
        exact hf ((semantic_isometry_affine_iff (tensorMap t B.operator.toLinearMap)
          (tensorMap_stabilizer t _ (clifford_semantic B)) f).mp h)
      have hc := column_form_actual_shortening t V a c M a₀ Q ha₀ hrank hroom hcol g hg
      have he : tensorMap t V g=tensorMap t U f := by
        simp only [V,g,tensorMap_comp,LinearMap.comp_apply,tensorMap_linearEquiv_cancel]
      rwa [he] at hc

end
end Holant.Platonic.StabilizerShortening
