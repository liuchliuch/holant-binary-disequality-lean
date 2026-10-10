import Holant.Platonic.StabilizerErasure.MixedStabilizerResidual

/-! The correctable-erasure clause of Lemma 9.20 in its full source sense.
Both residual maps are proved stabilizer isometries; the forms are mutually
exclusive, and the required one-port Clifford is actually constructed. -/
namespace Holant.Platonic.StabilizerErasure
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open Holant.Platonic.StabilizerLine Holant.Platonic.StabilizerCode
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n k : ℕ}

def PureStabilizerForm (T : Signature ℂ k →ₗ[ℂ] Signature ℂ (n+1)) (r : Fin (n+1)) : Prop :=
  ∃b : Bool,∃W : Signature ℂ k →ₗ[ℂ] Signature ℂ n,
    IsStabilizerIsometry W ∧ ∀f w,T f w=if w r=b then W f (r.removeNth w) else 0

def MixedStabilizerForm (T : Signature ℂ k →ₗ[ℂ] Signature ℂ (n+1)) (r : Fin (n+1)) : Prop :=
  ∃W : Signature ℂ (k+1) →ₗ[ℂ] Signature ℂ n,
    IsStabilizerIsometry W ∧
      ∀f b w,T f (r.insertNth b w)=(sqrtTwo : ℂ)⁻¹*W (auxiliaryKet b f) w

theorem pure_mixed_exclusive (T : Signature ℂ k →ₗ[ℂ] Signature ℂ (n+1))
    (r : Fin (n+1)) : ¬(PureStabilizerForm T r ∧ MixedStabilizerForm T r) := by
  rintro ⟨⟨b,W,hW,hpure⟩,⟨M,hM,hmixed⟩⟩
  have hb : (!b)≠b := by cases b <;> decide
  have hz : M (auxiliaryKet (!b) (fun _ => 1))=0 := by
    ext w
    have hp := hpure (fun _ => 1) (r.insertNth (!b) w)
    simp only [Fin.insertNth_apply_same,hb,ite_false] at hp
    have hm := hmixed (fun _ => 1) (!b) w
    rw [hp] at hm
    exact (mul_eq_zero.mp hm.symm).resolve_left
      (inv_ne_zero (by exact_mod_cast sqrtTwo_ne_zero))
  have hi := isometry_injective M hM.1
  have ha : auxiliaryKet (!b) (fun _ : Word k => (1 : ℂ))=0 := hi (by simpa using hz)
  have he := congrArg (column 0 (!b)) ha
  have hc : (fun _ : Word k => (1 : ℂ))=0 := by simpa using he
  exact one_signature_ne_zero hc

/-- Exactly one of the source's two forms after a fixed genuine one-qubit
Clifford. In the pure form the unary factor is the computational stabilizer
ket |b⟩; W's actual code image and logical representatives are proved. -/
theorem source_correctable_erasure_normal_forms (V : StabilizerIsometry k (n+1))
    (r : Fin (n+1)) (h : Correctable V r) :
    ∃C : AnalyticClifford (n+1),∃R : Kernel ℂ,
      (∀f,C.operator f=siteAction r R f) ∧
      (PureStabilizerForm (C.operator.toLinearMap.comp V.map) r ∨
        MixedStabilizerForm (C.operator.toLinearMap.comp V.map) r) ∧
      ¬(PureStabilizerForm (C.operator.toLinearMap.comp V.map) r ∧
        MixedStabilizerForm (C.operator.toLinearMap.comp V.map) r) := by
  obtain ⟨a,ha,_,hz|⟨p,hp,hap,ho⟩⟩ := correctable_expectation_dichotomy V r h
  · have he : ∀p : Fin 4,p≠0 → ∀f,V.adjoint (siteAction r (qubitPauli p) (V.map f))=0 := by
      intro p hp f
      rw [ha,hz p hp,zero_smul]
    refine ⟨Program.identity.clifford,qubitPauli 0,
      (fun f => (siteAction_qubitPauli_zero r f).symm),Or.inr ?_,pure_mixed_exclusive _ r⟩
    exact ⟨mixedResidual V r,mixedResidual_stabilizer V r he,mixed_column_expansion V r⟩
  · obtain ⟨C,R,hR,hC⟩ := exists_local_axis_clifford r p hp
    have han : a p≠0 := by rcases hap with hh|hh <;> rw [hh] <;> norm_num
    have he := V.scalar_nonzero_action (physicalPauli r p) (a p) han
      (by simpa only [physicalPauli_exact] using ha p)
    simp only [physicalPauli_exact] at he
    obtain ⟨b,hb⟩ : ∃b : Bool,a p=(if b then (-1 : ℂ) else 1) := by
      rcases hap with hh|hh
      · exact ⟨false,hh⟩
      · exact ⟨true,hh⟩
    have hZ (f : Signature ℂ k) :
        siteAction r (qubitPauli 3) ((V.postcompose C).map f)=
          (if b then (-1 : ℂ) else 1) • (V.postcompose C).map f := by
      rw [StabilizerIsometry.postcompose_map,←hC,he,map_smul,hb]
    refine ⟨C,R,hR,Or.inl ?_,pure_mixed_exclusive _ r⟩
    exact ⟨b,pureResidual (V.postcompose C) r b,pureResidual_stabilizer (V.postcompose C) r b hZ,
      pure_column_expansion (V.postcompose C) r b hZ⟩

end
end Holant.Platonic.StabilizerErasure
