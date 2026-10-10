import Holant.Certificates.AffineEndpoint.Phases
import Holant.Certificates.AffineEndpoint.PhaseCodes

/-! Uniqueness of the canonical intrinsic phase parameters. -/
namespace Holant.Certificates.AffineEndpoint
open Holant Holant.Tractable Holant.Tractable.AffinePhase
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

 theorem raw_fourth_powers_injective : Function.Injective
    (fun j : Fin 4 => OctahedralSeparator.imag^j.val) := by decide +kernel

 theorem fourthRootPhase_injective : Function.Injective fourthRootPhase := by
  intro q r h
  have he : algebraicEmbed (OctahedralSeparator.imag^q.val)=algebraicEmbed (OctahedralSeparator.imag^r.val) := by
    simpa only [algebraicEmbed_pow,algebraicEmbed_imag,fourthRootPhase] using h
  have hv : (⟨q.val,q.val_lt⟩ : Fin 4)=⟨r.val,r.val_lt⟩ :=
    raw_fourth_powers_injective (algebraicEmbed_injective he)
  exact ZMod.val_injective 4 (congrArg Fin.val hv)

 theorem phase_eval_basis {d : Nat} (p : PhaseParameters d) (j : Fin d) (hd : d ≤ 4) :
    (phaseQuadratic p).eval (basis j)=(p.1 j).val := by
  classical
  interval_cases d <;> fin_cases j <;>
    simp [phaseQuadratic,QuadraticPhase.eval,basis,bitValue,Fin.sum_univ_succ]

 theorem phase_eval_pair {d : Nat} (p : PhaseParameters d) (j k : Fin d) (hjk : j<k) (hd : d ≤ 4) :
    (phaseQuadratic p).eval (fun i => decide (i=j ∨ i=k))=
      (p.1 j).val+(p.1 k).val+(if p.2 ⟨(j,k),hjk⟩ then 2 else 0) := by
  classical
  interval_cases d <;> fin_cases j <;> fin_cases k <;> try omega
  all_goals norm_num at hjk
  all_goals simp [phaseQuadratic,QuadraticPhase.eval,bitValue,Fin.sum_univ_succ] <;> ring

 theorem phaseValue_injective_small (d : Nat) (hd : d ≤ 4) :
    Function.Injective (@phaseValue d) := by
  intro p q hpq
  have he (y : Word d) : (phaseQuadratic p).eval y=(phaseQuadratic q).eval y :=
    fourthRootPhase_injective (congrFun hpq y)
  have hl (j : Fin d) : p.1 j=q.1 j := by
    have h := he (basis j)
    rw [phase_eval_basis p j hd,phase_eval_basis q j hd] at h
    apply Fin.ext
    have hv := congrArg ZMod.val h
    simpa only [ZMod.val_natCast,Nat.mod_eq_of_lt (p.1 j).isLt,Nat.mod_eq_of_lt (q.1 j).isLt] using hv
  apply Prod.ext
  · exact funext hl
  · funext jk
    have h := he (fun i => decide (i=jk.val.1 ∨ i=jk.val.2))
    rw [phase_eval_pair p jk.val.1 jk.val.2 jk.property hd,
      phase_eval_pair q jk.val.1 jk.val.2 jk.property hd,hl jk.val.1,hl jk.val.2] at h
    have hc : (if p.2 jk then (2 : ZMod 4) else 0)=(if q.2 jk then 2 else 0) := add_left_cancel h
    have hi : Function.Injective (fun b : Bool => if b then (2 : ZMod 4) else 0) := by decide
    exact hi hc

 theorem phase_code_parameter_card (d : Nat) (hd : d ≤ 4) :
    Fintype.card (Fin (phaseCodeCount d))=Fintype.card (PhaseParameters d) := by
  simp only [PhaseParameters,Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,Fintype.card_bool]
  interval_cases d <;> decide +kernel

 theorem phaseDecode_injective_small (d : Nat) (hd : d ≤ 4) : Function.Injective (phaseDecode d) :=
  (Finite.injective_iff_surjective_of_equiv (Fintype.equivOfCardEq (phase_code_parameter_card d hd))).mpr
    (phaseDecode_surjective d)

end
end Holant.Certificates.AffineEndpoint
