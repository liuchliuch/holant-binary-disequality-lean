import Holant.ReedMuller.AffineRadon.Phase

/-! Exact fourth-root and binary graph algebra for the coefficient part of the
source affine-to-character-flat argument. No physical transport is asserted. -/
namespace Holant.ReedMuller.CharacterRecognition
open Holant Holant.Tractable Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.CharacterFlat
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The actual source fourth-root phase, faithfully embedded in `ℂ`. -/
def root (q : ZMod 4) : ℂ := (fourthRootPhase q : ℂ)
@[simp] theorem root_zero : root 0=1 := by simp [root]
@[simp] theorem root_one : root 1=Complex.I := by simp [root]
@[simp] theorem root_two : root 2= -1 := by simp [root]
@[simp] theorem root_three : root 3= -Complex.I := by simp [root]
theorem root_add (a b : ZMod 4) : root (a+b)=root a*root b := by
  simp [root,fourthRootPhase_add]
theorem root_ne_zero (q : ZMod 4) : root q≠0 := by
  change (fourthRootPhase q : ℂ)≠0
  exact_mod_cast fourthRootPhase_ne_zero q
@[simp] theorem root_evenLift (b : ZMod 2) : root (TwoTranslate.evenLift b)=sign b := by
  fin_cases b <;> simp

def Even (q : ZMod 4) : Prop := q=0 ∨ q=2
def Odd (q : ZMod 4) : Prop := q=1 ∨ q=3

theorem even_or_odd (q : ZMod 4) : Even q ∨ Odd q := by
  rcases TwoTranslate.fourth_cases q with rfl|rfl|rfl|rfl <;> simp [Even,Odd]

theorem even_of_root_square (q : ZMod 4) (h : root q ^ 2=1) : Even q := by
  rcases TwoTranslate.fourth_cases q with rfl|rfl|rfl|rfl <;> simp_all [Even] <;> norm_num at h

theorem odd_root_square (q : ZMod 4) (h : Odd q) : root q ^ 2= -1 := by
  rcases h with rfl|rfl <;> simp

theorem odd_bracket_ne_zero (q : ZMod 4) (hq : Odd q) (b : ZMod 2) :
    1+root q*sign b≠0 := by
  rcases hq with rfl|rfl <;> fin_cases b <;> simp
  all_goals intro h; have hh := congrArg Complex.re h; norm_num at hh

/-- The actual four coefficient identity of a full-support sign character
forces the manuscript's mixed-coefficient relation in an odd pair card. -/
theorem odd_rectangle_forces (q : ZMod 4) (hq : Odd q) (b c d : ZMod 2)
    (h : sign d*(1+root q)*(1+root q*sign (b+c))=
      (1+root q*sign b)*(1+root q*sign c)) : d=b*c := by
  simp only [sign_add] at h
  rcases hq with rfl|rfl <;> fin_cases b <;> fin_cases c <;> fin_cases d
  all_goals try rfl
  all_goals have hr := congrArg Complex.re h
  all_goals have hi := congrArg Complex.im h
  all_goals norm_num [Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im] at *

/-- Graph classification is valid for any finite index set; small arities are
included without manufacturing three distinct vertices. -/
theorem graph_empty_or_complete {ι : Type*} (beta : ι → ι → ZMod 2)
    (hsym : ∀ j k,beta j k=beta k j) (hdiag : ∀ j,beta j j=0)
    (hrel : ∀ j k m,j≠k → j≠m → k≠m → beta k m=beta j k*beta j m) :
    (∀ j k,beta j k=0) ∨ (∀ j k,j≠k → beta j k=1) := by
  classical
  by_cases hz : ∀ j k,beta j k=0
  · exact Or.inl hz
  right
  push_neg at hz
  obtain ⟨a,b,hab⟩ := hz
  have hab1 : beta a b=1 := (TwoTranslate.binary_cases (beta a b)).resolve_left hab
  have hne : a≠b := by intro h; subst b; exact hab (hdiag a)
  have ha (c : ι) (hc : c≠a) : beta a c=1 := by
    by_cases hcb : c=b
    · simpa [hcb] using hab1
    have hh := hrel c a b hc hcb hne
    rw [hab1] at hh
    rcases TwoTranslate.binary_cases (beta c a) with hz|ho
    · simp [hz] at hh
    · simpa [hsym a c] using ho
  intro j k hjk
  by_cases hja : j=a
  · subst j; exact ha k (Ne.symm hjk)
  by_cases hka : k=a
  · subst k; rw [hsym]; exact ha j hja
  rw [hrel a j k (Ne.symm hja) (Ne.symm hka) hjk,ha j hja,ha k hka,mul_one]

end
end Holant.ReedMuller.CharacterRecognition
