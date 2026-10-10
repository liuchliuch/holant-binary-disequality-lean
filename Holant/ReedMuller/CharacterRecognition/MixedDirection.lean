import Holant.ReedMuller.CharacterRecognition.Source

/-! A second, intrinsic coefficient route for 7.24: a two-basis direction
excludes the odd complete mixed graph. This uses an actual signed numerator,
not an outside-support physical kernel or a freely available coordinate gadget. -/
namespace Holant.ReedMuller.CharacterRecognition
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.CharacterFlat
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {r : ℕ}

def FullCharacter (f : Word r → ℂ) : Prop :=
  ∃ c : ℂ,c≠0 ∧ ∃ ell : Character r,∀ x,f x=c*sign (ell (vectorWord x))

def directionCard (Q : QuadraticPhase r) (w : Word r) (b : ZMod 2) (x : Word r) : ℂ :=
  phase Q x+sign b*phase Q (xor x w)

theorem FullCharacter.square {f : Word r → ℂ} (h : FullCharacter f) (x : Word r) :
    f x^2=f (origin r)^2 := by
  obtain ⟨c,hc,ell,he⟩ := h
  have hs : sign (ell (vectorWord x))^2=1 := by rw [pow_two,sign_square]
  simp only [he x,he (origin r),vectorWord_origin,map_zero,sign_zero,mul_one,mul_pow,hs]

theorem FullCharacter.slice {f : Word r → ℂ} (h : FullCharacter f) (j : Fin r) :
    SliceCharacter f j := by
  obtain ⟨c,hc,ell,he⟩ := h
  exact ⟨c,hc,ell,fun x _ => he x⟩

def ZeroOrFullCharacter (f : Word r → ℂ) : Prop :=
  (∀ x,f x=0) ∨ FullCharacter f

theorem zeroOrFullCharacter_smul_iff (c : ℂ) (hc : c≠0) (f : Word r → ℂ) :
    ZeroOrFullCharacter (fun x => c*f x) ↔ ZeroOrFullCharacter f := by
  constructor
  · rintro (hz|⟨d,hd,ell,he⟩)
    · exact Or.inl (fun x => (mul_eq_zero.mp (hz x)).resolve_left hc)
    · refine Or.inr ⟨d/c,div_ne_zero hd hc,ell,?_⟩
      intro x
      apply mul_left_cancel₀ hc
      have H : c*f x=d*sign (ell (vectorWord x)) := he x
      rw [H]
      field_simp
  · rintro (hz|⟨d,hd,ell,he⟩)
    · exact Or.inl (fun x => by change c*f x=0;rw [hz x,mul_zero])
    · exact Or.inr ⟨c*d,mul_ne_zero hc hd,ell,fun x => by change c*f x=(c*d)*sign (ell (vectorWord x));rw [he];ring⟩

theorem pairCards_of_full_directions (Q : QuadraticPhase r)
    (h : ∀ j l,ZeroOrFullCharacter (directionCard Q (basis j) l)) : PairCards Q := by
  intro j l
  rcases h j l with hz|hf
  · exact Or.inl (fun x _ => hz x)
  · exact Or.inr (hf.slice j)

theorem directionCard_origin (Q : QuadraticPhase r) (a b : Fin r) (hab : a≠b)
    (l : ZMod 2) : directionCard Q (xor (basis a) (basis b)) l (origin r)=
      1+sign l*(root (Q.linear a)*root (Q.linear b)*sign (beta Q a b)) := by
  simp only [directionCard,phase_origin,origin_xor,phase_two Q a b hab]

theorem directionCard_third (Q : QuadraticPhase r) (a b c : Fin r)
    (hab : a≠b) (hca : c≠a) (hcb : c≠b) (l : ZMod 2)
    (hac : beta Q c a=1) (hbc : beta Q c b=1) :
    directionCard Q (xor (basis a) (basis b)) l (basis c)=
      root (Q.linear c)*directionCard Q (xor (basis a) (basis b)) l (origin r) := by
  rw [directionCard_origin Q a b hab]
  unfold directionCard
  rw [phase_basis,xor_comm (basis c),phase_three Q c a b hca hcb hab,hac,hbc]
  simp only [sign_one]
  ring

/-- Plus and minus cannot both vanish at the original zero coefficient. -/
theorem exists_direction_sign (Q : QuadraticPhase r) (w : Word r) :
    ∃ l : ZMod 2,directionCard Q w l (origin r)≠0 := by
  by_cases h : directionCard Q w 0 (origin r)=0
  · refine ⟨1,?_⟩
    intro hn
    simp only [directionCard,phase_origin,origin_xor,sign_zero,sign_one,one_mul,neg_mul] at h hn
    have he : (2 : ℂ)=0 := by linear_combination h+hn
    norm_num at he
  · exact ⟨0,h⟩

theorem odd_complete_direction_contradiction {Q : QuadraticPhase r}
    (a b c : Fin r) (hab : a≠b) (hca : c≠a) (hcb : c≠b)
    (ho : Odd (Q.linear c)) (hac : beta Q c a=1) (hbc : beta Q c b=1)
    (hd : ∀ l,(∀ x,directionCard Q (xor (basis a) (basis b)) l x=0) ∨
      FullCharacter (directionCard Q (xor (basis a) (basis b)) l)) : False := by
  obtain ⟨l,hl⟩ := exists_direction_sign Q (xor (basis a) (basis b))
  rcases hd l with hz|hc
  · exact hl (hz _)
  have hh := hc.square (basis c)
  rw [directionCard_third Q a b c hab hca hcb l hac hbc,mul_pow,odd_root_square _ ho] at hh
  have hz : directionCard Q (xor (basis a) (basis b)) l (origin r)^2=0 := by
    linear_combination (-1/2 : ℂ)*hh
  exact pow_ne_zero 2 hl hz

/-- The source logical phase becomes a sign character from actual one-basis
and two-basis signed numerators. The mixed direction is a genuine accessible
ambient direction only after the separately proved embedding transport. -/
theorem phase_character_of_pair_and_mixed_cards (Q : QuadraticPhase r) (h : PairCards Q)
    (a b c : Fin r) (hab : a≠b) (hca : c≠a) (hcb : c≠b)
    (hd : ∀ l,(∀ x,directionCard Q (xor (basis a) (basis b)) l x=0) ∨
      FullCharacter (directionCard Q (xor (basis a) (basis b)) l)) :
    ∃ ell : Character r,∀ x,phase Q x=sign (ell (vectorWord x)) := by
  rcases coefficient_dichotomy h with ⟨he,hz⟩|⟨ho,hgraph⟩
  · exact phase_character_of_even_empty Q he hz
  rcases hgraph with hz|hc
  · exact False.elim (odd_empty_contradiction h ho hz a b hab)
  · exact False.elim (odd_complete_direction_contradiction a b c hab hca hcb
      (ho c) (hc c a hca) (hc c b hcb) hd)

end
end Holant.ReedMuller.CharacterRecognition
