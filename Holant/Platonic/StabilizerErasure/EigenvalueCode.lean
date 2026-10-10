import Holant.Platonic.StabilizerErasure.SemanticClosure

/-! The source permits a fourth-root eigenvalue character on its commuting
Pauli subgroup. Absorbing those actual phases into the actual Pauli
generators gives precisely the common +1 image definition used here. -/
namespace Holant.Platonic.StabilizerErasure
open Holant Holant.Platonic.StabilizerLine Holant.Platonic.StabilizerCode
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {n k : ℕ}

def HasPauliEigenspaceImage (U : Signature ℂ k →ₗ[ℂ] Signature ℂ n) : Prop :=
  ∃t : ℕ,∃P : Fin t → Pauli n,∃q : Fin t → ZMod 4,
    (∀i j f,(P i).run ((P j).run f)=(P j).run ((P i).run f)) ∧
    ∀f,f∈LinearMap.range U ↔ ∀i,(P i).run f=phaseRoot (q i) • f

theorem hasStabilizerImage_iff_eigenvalues (U : Signature ℂ k →ₗ[ℂ] Signature ℂ n) :
    HasStabilizerImage U ↔ HasPauliEigenspaceImage U := by
  constructor
  · rintro ⟨t,P,hcomm,hcode⟩
    exact ⟨t,P,fun _ => 0,hcomm,by simpa using hcode⟩
  · rintro ⟨t,P,q,hcomm,hcode⟩
    let R := fun i => pauliShiftPhase (-q i) (P i)
    have hf (i : Fin t) (f : Signature ℂ n) :
        (R i).run f=f ↔ (P i).run f=phaseRoot (q i) • f := by
      constructor
      · intro h
        have he := congrArg (fun g : Signature ℂ n => phaseRoot (q i) • g) h
        simp only [R,pauliShiftPhase_run,smul_smul,←phaseRoot_add,add_neg_cancel,
          phaseRoot_zero,one_smul] at he
        exact he
      · intro h
        simp only [R,pauliShiftPhase_run,h,smul_smul,←phaseRoot_add,neg_add_cancel,
          phaseRoot_zero,one_smul]
    refine ⟨t,R,?_,?_⟩
    · intro i j f
      simp only [R,pauliShiftPhase_run,pauli_run_smul,smul_smul]
      rw [hcomm]
      congr 1
      ring
    · intro f
      rw [hcode]
      exact forall_congr' (fun i => (hf i f).symm)

end
end Holant.Platonic.StabilizerErasure
