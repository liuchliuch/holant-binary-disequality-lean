import Holant.Platonic.StabilizerErasure.BellPostselection

/-! Exact amplitudes of the two Bell projections, retaining their positive
normalization and the original logical auxiliary input ordering. -/
namespace Holant.Platonic.StabilizerErasure
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open Holant.ReedMuller.FlatNetwork Holant.ReedMuller.CharacterFlat
open Holant.Platonic.StabilizerLine Holant.Platonic.StabilizerCode
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n k : ℕ}

theorem sqrtTwo_complex_sq : (sqrtTwo : ℂ)^2=2 := by
  change (Real.sqrt 2 : ℂ)^2=2
  norm_cast
  exact Real.sq_sqrt (by norm_num)

theorem sqrtTwo_complex_inv_sq : ((sqrtTwo : ℂ)⁻¹)^2=(1/2 : ℂ) := by
  rw [inv_pow,sqrtTwo_complex_sq]
  norm_num

theorem physicalZ_insert (r : Fin (n+1)) (f : Signature ℂ (n+1)) (b : Bool) (w : Word n) :
    (physicalPauli r 3).run f (r.insertNth b w)=sign (boolEquiv b)*f (r.insertNth b w) := by
  rw [physicalPauli_exact]
  cases b <;> simp [siteAction,qubitPauli,boolEquiv]

theorem physicalX_insert (r : Fin (n+1)) (f : Signature ℂ (n+1)) (b : Bool) (w : Word n) :
    (physicalPauli r 1).run f (r.insertNth b w)=f (r.insertNth (!b) w) := by
  rw [physicalPauli_exact]
  cases b <;> simp [siteAction,qubitPauli]

theorem bellZ_insert (r : Fin (n+1)) (f : Signature ℂ (n+2)) (b c : Bool) (w : Word n) :
    (bellZ r).run f (Fin.cons b (r.insertNth c w))=
      sign (boolEquiv b)*sign (boolEquiv c)*f (Fin.cons b (r.insertNth c w)) := by
  have he := congrFun (column_prependPauli 0 1 (physicalPauli r 3) b f) (r.insertNth c w)
  simp only [Pi.smul_apply,smul_eq_mul,one_mul,add_zero,Equiv.symm_apply_apply,
    column_zero_apply,physicalZ_insert] at he
  simpa only [bellZ,mul_assoc] using he

theorem bellX_insert (r : Fin (n+1)) (f : Signature ℂ (n+2)) (b c : Bool) (w : Word n) :
    (bellX r).run f (Fin.cons b (r.insertNth c w))=
      f (Fin.cons (!b) (r.insertNth (!c) w)) := by
  have he := congrFun (column_prependPauli 1 0 (physicalPauli r 1) b f) (r.insertNth c w)
  simp only [Pi.smul_apply,smul_eq_mul,zero_mul,ReedMuller.CharacterFlat.sign_zero,one_mul,
    column_zero_apply,physicalX_insert] at he
  cases b <;> simpa [bellX,boolEquiv] using he

theorem positivePostselect_apply (P : Pauli n) (U : Signature ℂ k →ₗ[ℂ] Signature ℂ n)
    (f : Signature ℂ k) (w : Word n) :
    positivePostselect P U f w=(sqrtTwo : ℂ)⁻¹*(U f w+P.run (U f) w) := rfl

theorem bellProjected_apply (V : StabilizerIsometry k (n+1)) (r : Fin (n+1))
    (f : Signature ℂ (k+1)) (b c : Bool) (w : Word n) :
    bellProjected V r f (Fin.cons b (r.insertNth c w))=
      if b=c then V.map (column 0 false f) (r.insertNth false w)+
        V.map (column 0 true f) (r.insertNth true w) else 0 := by
  unfold bellProjected
  rw [positivePostselect_apply,bellX_insert,positivePostselect_apply,positivePostselect_apply,
    bellZ_insert,bellZ_insert]
  simp only [prependMap,LinearMap.coe_mk,AddHom.coe_mk,Fin.cons_zero,Fin.tail_cons]
  cases b <;> cases c <;> simp [boolEquiv] <;> ring_nf <;>
    (try simp only [show ((Real.sqrt 2 : ℂ)⁻¹)^2=(1/2 : ℂ) from sqrtTwo_complex_inv_sq]) <;> ring

theorem bellProjected_mixedResidual (V : StabilizerIsometry k (n+1)) (r : Fin (n+1))
    (f : Signature ℂ (k+1)) (b c : Bool) (w : Word n) :
    bellProjected V r f (Fin.cons b (r.insertNth c w))=
      if b=c then (sqrtTwo : ℂ)⁻¹*mixedResidual V r f w else 0 := by
  rw [bellProjected_apply,mixedResidual_apply]
  cases b <;> cases c <;> simp [column]
  all_goals
    have hs : (Real.sqrt 2 : ℂ)≠0 := by exact_mod_cast Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ)<2)
    field_simp [hs]
    ring

end
end Holant.Platonic.StabilizerErasure
