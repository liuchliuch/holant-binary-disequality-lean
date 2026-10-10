import Holant.Platonic.StabilizerLine.Basic

/-! Equivalence with the literal source affine formula over arbitrary complex
amplitudes. The algebraic implementation is only a phase/support carrier. -/
namespace Holant.Platonic.StabilizerLine
open Holant Holant.Tractable Holant.Tractable.AffinePhase
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

def complexAffineFormula (c : ℂ) (S : AffineSystem n) (Q : QuadraticPhase n) : Signature ℂ n :=
  fun x => if S.Holds x then c*(fourthRootPhase (Q.eval x):ℂ) else 0

theorem complexAffine_formula (c : ℂ) (S : AffineSystem n) (Q : QuadraticPhase n) :
    ComplexAffine (complexAffineFormula c S Q) := by
  refine ⟨c,affineFormula 1 S Q,affine_formula 1 S Q,?_⟩
  intro x
  simp only [complexAffineFormula,affineFormula,one_mul]
  by_cases h : S.Holds x <;> simp [h]

theorem complexAffine_iff_literal (f : Signature ℂ n) :
    ComplexAffine f ↔ f=0 ∨ ∃ c : ℂ,c≠0 ∧ ∃ S : AffineSystem n,
      ∃ Q : QuadraticPhase n,f=complexAffineFormula c S Q := by
  constructor
  · rintro ⟨c,g,hg,he⟩
    by_cases hz : c=0
    · left;funext x;simp [he,hz]
    rcases hg with h0|⟨a,ha,S,Q,hg⟩
    · left;funext x;simp [he,h0]
    · right
      refine ⟨c*(a:ℂ),mul_ne_zero hz (by exact_mod_cast ha),S,Q,?_⟩
      funext x
      rw [he,hg]
      by_cases hx : S.Holds x <;> simp [complexAffineFormula,affineFormula,hx,mul_assoc]
  · rintro (h|⟨c,hc,S,Q,h⟩)
    · subst f
      exact ⟨0,0,affine_zero n,by simp⟩
    · rw [h]
      exact complexAffine_formula c S Q

end
end Holant.Platonic.StabilizerLine
