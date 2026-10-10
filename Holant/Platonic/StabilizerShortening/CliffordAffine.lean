import Holant.Platonic.StabilizerShortening.CliffordAffinePhase
import Holant.Platonic.StabilizerErasure.SemanticEncoderFactorization

/-! Affine preservation and reflection for actual arbitrary Pauli-normalizing
unitaries and source-primary stabilizer isometries. Analytic coordinate changes
are not asserted to be physical Holant resources. -/
namespace Holant.Platonic.StabilizerShortening
open Holant Holant.Tractable Holant.Tractable.AffinePhase Holant.Tractable.TwoTranslate
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.AffinePatching Holant.ReedMuller.CharacterFlat
open Holant.Platonic.StabilizerLine Holant.Platonic.StabilizerCode
open Holant.Platonic.StabilizerErasure
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n k a : ℕ}

private theorem delta_ne_zero : (delta : Signature ℂ n)≠0 := by
  intro h
  have hh := congrFun h (origin n)
  simpa [delta] using hh

/-- Every actual analytic Clifford sends the computational zero ket to an
actual affine state, by its Pauli fixed space rather than assumed synthesis. -/
theorem clifford_delta_affine (C : AnalyticClifford n) : ComplexAffine (C.operator delta) :=
  complexAffine_of_unique_fixed _ (clifford_delta_unique C)
    (by intro h; exact delta_ne_zero (C.operator.injective (by simpa using h)))

/-- The normalizer definition itself suffices; no Program presentation is needed. -/
theorem analyticClifford_affine (C : AnalyticClifford n) (f : Signature ℂ n)
    (hf : ComplexAffine f) : ComplexAffine (C.operator f) := by
  by_cases hn : f=0
  · subst f
    refine ⟨0,0,affine_zero n,?_⟩
    intro w
    simp
  · obtain ⟨P,c,hc,hP⟩ := exists_normalizing_program f hf hn
    let D := alignmentCompose C (inverseClifford P.clifford)
    have hd := clifford_delta_affine D
    have hp : P.clifford.operator f=c • delta := by
      change P.run f=(fun x => c*delta x)
      exact hP
    have he : C.operator f=c • D.operator delta := by
      have h := congrArg (fun w => C.operator (P.clifford.operator.symm w)) hp
      change C.operator f=c • C.operator (P.clifford.operator.symm delta)
      simpa only [LinearEquiv.symm_apply_apply,map_smul] using h
    rw [he]
    exact hd.scale c

theorem analyticClifford_affine_iff (C : AnalyticClifford n) (f : Signature ℂ n) :
    ComplexAffine (C.operator f) ↔ ComplexAffine f := by
  constructor
  · intro h
    have hh := analyticClifford_affine (inverseClifford C) (C.operator f) h
    simpa [inverseClifford] using hh
  · exact analyticClifford_affine C f

private theorem pullback_affine {m : ℕ} (f : Signature ℂ n) (hf : ComplexAffine f)
    (p : Word m → Word n) (hp : IsAffineMap p) : ComplexAffine (fun w => f (p w)) := by
  obtain ⟨c,g,hg,he⟩ := hf
  exact ⟨c,fun w => g (p w),hg.precompose p hp,fun w => he (p w)⟩

/-- Initializing actual zero ancillas preserves the source support/phase predicate. -/
theorem attachZero_affine
    (e : BinaryVector n ≃ₗ[ZMod 2] BinaryVector k × BinaryVector a)
    (f : Signature ℂ k) (hf : ComplexAffine f) : ComplexAffine (attachZero e f) := by
  obtain ⟨c,g,hg,he⟩ := hf
  let p : Word n → Word k := affineBoolean 0 (leftCoordinates e)
  let S := supportSystem e 0
  refine ⟨c,fun w => if S.Holds w then g (p w) else 0,
    (hg.precompose p (affineBoolean_isAffine 0 (leftCoordinates e))).restrict S,?_⟩
  intro w
  have hs : S.Holds w ↔ (e (vectorWord w)).2=0 := by
    simpa [S] using supportSystem_holds e 0 w
  by_cases hw : (e (vectorWord w)).2=0
  · simp [attachZero,hs,hw,p,affineBoolean,leftCoordinates,he]
  · simp [attachZero,hs,hw]

/-- The actual zero-ancilla evaluation is an affine Boolean pullback. -/
theorem evaluateZero_affine
    (e : BinaryVector n ≃ₗ[ZMod 2] BinaryVector k × BinaryVector a)
    (f : Signature ℂ n) (hf : ComplexAffine f) : ComplexAffine (evaluateZero e f) := by
  let M := e.symm.toLinearMap.comp (LinearMap.inl (ZMod 2) (BinaryVector k) (BinaryVector a))
  have h := pullback_affine f hf (affineBoolean 0 M) (affineBoolean_isAffine 0 M)
  simpa [evaluateZero,affineBoolean,M] using h

theorem encoder_affine_iff (V : StabilizerIsometry k n) (f : Signature ℂ k) :
    ComplexAffine (V.map f) ↔ ComplexAffine f := by
  constructor
  · intro h
    have hh := (analyticClifford_affine_iff V.clifford (attachZero V.coordinates f)).mp h
    simpa using evaluateZero_affine V.coordinates (attachZero V.coordinates f) hh
  · intro h
    exact analyticClifford_affine V.clifford _ (attachZero_affine V.coordinates f h)

/-- Full source-primary isometry preservation and reflection; the concrete
encoder and logical Clifford are constructed inside the proof. -/
theorem semantic_isometry_affine_iff
    (U : Signature ℂ k →ₗ[ℂ] Signature ℂ n) (hU : IsStabilizerIsometry U)
    (f : Signature ℂ k) : ComplexAffine (U f) ↔ ComplexAffine f := by
  obtain ⟨V,L,hUL⟩ := semantic_encoder_clifford_factorization U hU
  rw [hUL]
  change ComplexAffine (V.map (L.operator f)) ↔ ComplexAffine f
  rw [encoder_affine_iff,analyticClifford_affine_iff]

end
end Holant.Platonic.StabilizerShortening
