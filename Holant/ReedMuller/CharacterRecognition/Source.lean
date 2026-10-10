import Holant.ReedMuller.CharacterRecognition.Recognition

/-! An honest coefficient interface for the paired-support stage of source
Lemma 7.24. All inputs below concern literal unnormalized source coefficients.

Remaining geometric transport: (1) translate and orthogonally identify the
actual self-dual support with `Pair_r`; (2) pull the phase back to a genuine
`Tractable.QuadraticPhase r`; (3) obtain zero-or-full slice character equations
from character-flat physical quotient cards, using their support dimension;
(4) identify an outside-pair quotient card on `t_a+t_b=0`. This file proves
only the ensuing coefficient recognition, and claims no numbered theorem. -/
namespace Holant.ReedMuller.CharacterRecognition
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.CharacterFlat
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {r : ℕ}

/-- The actual input coefficient, including its nonzero external scale. -/
def coefficient (scale : ℂ) (Q : QuadraticPhase r) (x : Word r) : ℂ :=
  scale*root (Q.eval x)

/-- The signed logical pair-card numerator from the original coefficients. -/
def sourceCard (scale : ℂ) (Q : QuadraticPhase r) (j : Fin r) (b : ZMod 2)
    (x : Word r) : ℂ :=
  coefficient scale Q x+sign b*coefficient scale Q (xor x (basis j))

/-- Literal coefficient sums, with no assumed phase-coefficient conclusions. -/
def SourcePairCards (scale : ℂ) (Q : QuadraticPhase r) : Prop := ∀ j b,
  (∀ x,x j=false → sourceCard scale Q j b x=0) ∨
    SliceCharacter (sourceCard scale Q j b) j

/-- The actual supported coefficients of one outside-pair card. -/
def SourceOutsidePairCharacter (scale : ℂ) (Q : QuadraticPhase r) (a b : Fin r) : Prop :=
  ∃ c : ℂ, c≠0 ∧ ∃ ell : Character r, ∀ x,
    boolEquiv (x a)+boolEquiv (x b)=0 →
      coefficient scale Q x=c*sign (ell (vectorWord x))

theorem coefficient_normalized (scale : ℂ) (Q : QuadraticPhase r) (x : Word r) :
    coefficient scale Q x=(scale*root Q.constant)*phase Q x := by
  rw [coefficient,source_phase,mul_assoc]

theorem sourceCard_normalized (scale : ℂ) (Q : QuadraticPhase r)
    (j : Fin r) (b : ZMod 2) (x : Word r) :
    sourceCard scale Q j b x=(scale*root Q.constant)*card Q j b x := by
  simp only [sourceCard,coefficient_normalized,card]
  ring

theorem SourcePairCards.normalize {scale : ℂ} {Q : QuadraticPhase r}
    (h : SourcePairCards scale Q) (hs : scale≠0) : PairCards Q := by
  have hc := mul_ne_zero hs (root_ne_zero Q.constant)
  intro j b
  rcases h j b with hz|⟨c,hc',ell,he⟩
  · left
    intro x hx
    have hh := hz x hx
    rw [sourceCard_normalized] at hh
    exact (mul_eq_zero.mp hh).resolve_left hc
  · right
    refine ⟨c/(scale*root Q.constant),div_ne_zero hc' hc,ell,?_⟩
    intro x hx
    have hh := he x hx
    rw [sourceCard_normalized] at hh
    apply mul_left_cancel₀ hc
    calc
      (scale*root Q.constant)*card Q j b x=c*sign (ell (vectorWord x)) := hh
      _=(scale*root Q.constant)*(c/(scale*root Q.constant)*sign (ell (vectorWord x))) := by
        field_simp [hs,root_ne_zero Q.constant]

theorem SourceOutsidePairCharacter.normalize {scale : ℂ} {Q : QuadraticPhase r}
    {a b : Fin r} (h : SourceOutsidePairCharacter scale Q a b) (hs : scale≠0) :
    OutsidePairCharacter Q a b := by
  have hc := mul_ne_zero hs (root_ne_zero Q.constant)
  obtain ⟨c,hc',ell,he⟩ := h
  refine ⟨c/(scale*root Q.constant),div_ne_zero hc' hc,ell,?_⟩
  intro x hx
  have hh := he x hx
  rw [coefficient_normalized] at hh
  apply mul_left_cancel₀ hc
  calc
    (scale*root Q.constant)*phase Q x=c*sign (ell (vectorWord x)) := hh
    _=(scale*root Q.constant)*(c/(scale*root Q.constant)*sign (ell (vectorWord x))) := by
      field_simp [hs,root_ne_zero Q.constant]

/-- Paired-coordinate recognition from actual signed coefficient sums.
The output scalar is explicitly the original scalar times the constant phase. -/
theorem coefficient_character_of_source_cards (scale : ℂ) (hs : scale≠0)
    (Q : QuadraticPhase r) (h : SourcePairCards scale Q)
    (a b c : Fin r) (hab : a≠b) (hca : c≠a) (hcb : c≠b)
    (hout : SourceOutsidePairCharacter scale Q a b) :
    ∃ ell : Character r,∀ x,
      coefficient scale Q x=(scale*root Q.constant)*sign (ell (vectorWord x)) := by
  obtain ⟨ell,hell⟩ := source_phase_character_of_cards Q (h.normalize hs)
    a b c hab hca hcb (hout.normalize hs)
  refine ⟨ell,?_⟩
  intro x
  rw [coefficient,hell,mul_assoc]

end
end Holant.ReedMuller.CharacterRecognition
