import Holant.Platonic.StabilizerErasure.SemanticFullSource
import Holant.Platonic.StabilizerShortening.InverseAxes

/-! Refine the established erasure dichotomy to the actual finite axis
frames in its constructive proof. The maximally mixed case needs no frame
at all, so its Bell card uses the literal physical Q0 representative. -/
namespace Holant.Platonic.StabilizerShortening
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open Holant.Platonic.StabilizerLine Holant.Platonic.StabilizerCode
open Holant.Platonic.StabilizerErasure
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {k n : ℕ}

def PureAxisForm (U : Signature ℂ k →ₗ[ℂ] Signature ℂ (n+1))
    (r : Fin (n+1)) : Prop :=
  ∃p : Fin 4,PureStabilizerForm ((axisProgram r p).clifford.operator.toLinearMap.comp U) r

theorem axisProgram_intertwines (r : Fin (n+1)) (p : Fin 4) (hp : p≠0)
    (f : Signature ℂ (n+1)) :
    (axisProgram r p).clifford.operator (siteAction r (qubitPauli p) f)=
      siteAction r (qubitPauli 3) ((axisProgram r p).clifford.operator f) := by
  simp only [Program.clifford_apply,axisProgram_exact,siteAction_mul]
  rw [axisMatrix_intertwines p hp]

theorem encoder_correctable_axis_or_mixed (V : StabilizerIsometry k (n+1))
    (r : Fin (n+1)) (h : Correctable V r) : PureAxisForm V.map r ∨ MixedStabilizerForm V.map r := by
  obtain ⟨a,ha,_,hz|⟨p,hp,hap,ho⟩⟩ := correctable_expectation_dichotomy V r h
  · have he : ∀p : Fin 4,p≠0 → ∀f,V.adjoint (siteAction r (qubitPauli p) (V.map f))=0 := by
      intro p hp f
      rw [ha,hz p hp,zero_smul]
    exact Or.inr ⟨mixedResidual V r,mixedResidual_stabilizer V r he,mixed_column_expansion V r⟩
  · have han : a p≠0 := by rcases hap with hh|hh <;> rw [hh] <;> norm_num
    have he := V.scalar_nonzero_action (physicalPauli r p) (a p) han
      (by simpa only [physicalPauli_exact] using ha p)
    simp only [physicalPauli_exact] at he
    obtain ⟨b,hb⟩ : ∃b : Bool,a p=(if b then (-1 : ℂ) else 1) := by
      rcases hap with hh|hh
      · exact ⟨false,hh⟩
      · exact ⟨true,hh⟩
    let C := (axisProgram r p).clifford
    have hZ (f : Signature ℂ k) :
        siteAction r (qubitPauli 3) ((V.postcompose C).map f)=
          (if b then (-1 : ℂ) else 1) • (V.postcompose C).map f := by
      rw [StabilizerIsometry.postcompose_map,←axisProgram_intertwines r p hp,he,map_smul,hb]
    exact Or.inl ⟨p,b,pureResidual (V.postcompose C) r b,
      pureResidual_stabilizer (V.postcompose C) r b hZ,pure_column_expansion (V.postcompose C) r b hZ⟩

/-- An arbitrary source-semantic encoder has a finite-axis pure factor or
the exact mixed expansion in the unchanged physical coordinates. -/
theorem semantic_correctable_axis_or_mixed
    (U : Signature ℂ k →ₗ[ℂ] Signature ℂ (n+1)) (hU : IsStabilizerIsometry U)
    (r : Fin (n+1)) (h : CorrectableMap U r) : PureAxisForm U r ∨ MixedStabilizerForm U r := by
  obtain ⟨V,L,hfactor⟩ := semantic_encoder_clifford_factorization U hU
  have hc : Correctable V r := by
    rw [hfactor,correctableMap_precompose,correctableMap_encoder] at h
    exact h
  rcases encoder_correctable_axis_or_mixed V r hc with ⟨p,hp⟩|hm
  · left
    refine ⟨p,?_⟩
    rw [hfactor]
    exact pureForm_precompose _ r L hp
  · right
    rw [hfactor]
    exact mixedForm_precompose _ r L hm

/-- Undo the finite local frame on the original physical port. The pure
residual yields a literal unary tensor separation before any card is taken. -/
theorem pureAxisForm_separation
    (U : Signature ℂ k →ₗ[ℂ] Signature ℂ (n+1)) (r : Fin (n+1))
    (h : PureAxisForm U r) :
    ∃u : Bool → ℂ,∃W : Signature ℂ k →ₗ[ℂ] Signature ℂ n,
      IsStabilizerIsometry W ∧ ∀f w,U f w=u (w r)*W f (r.removeNth w) := by
  obtain ⟨p,b,W,hW,he⟩ := h
  refine ⟨fun a=>inverseAxis p a b,W,hW,?_⟩
  intro f w
  have hc : siteAction r (inverseAxis p) (siteAction r (axisMatrix p) (U f))=U f := by
    rw [siteAction_mul,inverseAxis_mul_axis]
    ext x
    cases x r <;> simp [siteAction,Signature.equality]
  have hp (x : Word (n+1)) : siteAction r (axisMatrix p) (U f) x=
      if x r=b then W f (r.removeNth x) else 0 := by
    simpa only [LinearMap.comp_apply,LinearEquiv.coe_coe,Program.clifford_apply,
      axisProgram_exact] using he f x
  rw [←hc]
  change (∑a : Bool,inverseAxis p (w r) a*
    siteAction r (axisMatrix p) (U f) (r.insertNth a (r.removeNth w)))=_
  simp only [hp]
  cases b <;> simp

end
end Holant.Platonic.StabilizerShortening
