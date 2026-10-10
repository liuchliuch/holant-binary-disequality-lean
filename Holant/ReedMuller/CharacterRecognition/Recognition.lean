import Holant.ReedMuller.CharacterRecognition.Cards

/-! Logical-coordinate coefficient recognition. This is deliberately not a
numbered source theorem: orthogonal support reduction and the physical signed
quotient-card transports remain separate obligations. -/
namespace Holant.ReedMuller.CharacterRecognition
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.CharacterFlat
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
variable {r : ℕ}

/-- The coefficient presentation of the outside-pair plus card on its actual
supported layer. The physical orbit has only one supported endpoint, so the
coefficient is precisely the input phase. -/
def OutsidePairCharacter (Q : QuadraticPhase r) (a b : Fin r) : Prop :=
  ∃ c : ℂ, c≠0 ∧ ∃ ell : Character r, ∀ x,
    boolEquiv (x a)+boolEquiv (x b)=0 → phase Q x=c*sign (ell (vectorWord x))

/-- The empty mixed graph cannot coexist with odd linear phases and a full
sign-character pair card when two logical coordinates are available. -/
theorem odd_empty_contradiction {Q : QuadraticPhase r} (h : PairCards Q)
    (ho : ∀ j,Odd (Q.linear j)) (hz : ∀ j k,beta Q j k=0)
    (j k : Fin r) (hjk : j≠k) : False := by
  have hb := odd_bracket_ne_zero (Q.linear j) (ho j) 0
  simp only [sign_zero,mul_one] at hb
  have hf := h.full_of_origin j 0 (by simpa using hb)
  have hh := hf.square (basis k) (by simp [basis,hjk])
  rw [card_basis Q j k 0 hjk,card_origin,hz j k] at hh
  simp only [sign_zero,one_mul,mul_one,mul_pow,odd_root_square _ (ho k)] at hh
  have he : (1+root (Q.linear j))^2=0 := by linear_combination (-1/2 : ℂ)*hh
  exact pow_ne_zero 2 hb he

/-- This is the complete-graph outside-pair contradiction in the source.
The argument is stronger: once the actual outside-card presentation is known,
only oddness of the third linear phase is needed, independently of beta. -/
theorem outside_pair_odd_contradiction {Q : QuadraticPhase r} {a b : Fin r}
    (h : OutsidePairCharacter Q a b) (c : Fin r) (hca : c≠a) (hcb : c≠b)
    (ho : Odd (Q.linear c)) : False := by
  obtain ⟨s,hs,ell,he⟩ := h
  have h0 := he (origin r) (by rfl)
  simp only [phase_origin,vectorWord_origin,map_zero,sign_zero,mul_one] at h0
  have hc := he (basis c) (by simp [basis,Ne.symm hca,Ne.symm hcb,boolEquiv])
  rw [phase_basis,←h0,one_mul] at hc
  have hh : root (Q.linear c)^2=1 := by rw [hc,pow_two,sign_square]
  rw [odd_root_square _ ho] at hh
  norm_num at hh

/-- Actual pair cards plus one outside-pair card force the even/empty branch. -/
theorem even_empty_of_cards {Q : QuadraticPhase r} (h : PairCards Q)
    (a b c : Fin r) (hab : a≠b) (hca : c≠a) (hcb : c≠b)
    (hout : OutsidePairCharacter Q a b) :
    (∀ j,Even (Q.linear j)) ∧ ∀ j k,beta Q j k=0 := by
  rcases coefficient_dichotomy h with he|⟨ho,hgraph⟩
  · exact he
  rcases hgraph with hz|hc
  · exact False.elim (odd_empty_contradiction h ho hz a b hab)
  · exact False.elim (outside_pair_odd_contradiction hout c hca hcb (ho c))

/-- Every even source coefficient has an exact binary lift. -/
theorem even_binary_lift (q : ZMod 4) (hq : Even q) :
    ∃ b : ZMod 2,TwoTranslate.evenLift b=q := by
  rcases hq with rfl|rfl
  · exact ⟨0,rfl⟩
  · exact ⟨1,rfl⟩

/-- Construct the actual linear map defining the resulting sign character. -/
theorem phase_character_of_even_empty (Q : QuadraticPhase r)
    (he : ∀ j,Even (Q.linear j)) (hz : ∀ j k,beta Q j k=0) :
    ∃ ell : Character r,∀ x,phase Q x=sign (ell (vectorWord x)) := by
  classical
  choose a ha using fun j => even_binary_lift (Q.linear j) (he j)
  refine ⟨dotBilinear a,?_⟩
  intro x
  have hm (j k : Fin r) (hjk : j<k) : Q.mixed j k=0 := by
    have hh := evenLift_beta Q j k
    rw [hz j k,TwoTranslate.evenLift_zero] at hh
    simpa [mixed,hjk] using hh.symm
  have hterm (j : Fin r) :
      Q.linear j*bitValue (ZMod 4) (x j)=
        TwoTranslate.evenLift (a j*bitValue (ZMod 2) (x j)) := by
    cases x j <;> simp [ha]
  have hphase : Q.eval x-Q.constant=TwoTranslate.evenLift (TwoTranslate.dot a x) := by
    simp only [QuadraticPhase.eval]
    have hmix : (∑ j : Fin r,∑ k : Fin r,
        if j<k then Q.mixed j k*bitValue (ZMod 4) (x j)*bitValue (ZMod 4) (x k) else 0)=0 := by
      apply Finset.sum_eq_zero
      intro j hj
      apply Finset.sum_eq_zero
      intro k hk
      split_ifs with h
      · simp [hm j k h]
      · rfl
    rw [hmix,add_zero,add_sub_cancel_left]
    simp only [TwoTranslate.dot,TwoTranslate.evenLift_sum,hterm]
  rw [phase,hphase,root_evenLift]
  congr 1

/-- The public logical coefficient conclusion retains the original constant
phase and uses the repository's actual `CharacterFlat.Character` and sign. -/
theorem source_phase_character_of_cards (Q : QuadraticPhase r) (h : PairCards Q)
    (a b c : Fin r) (hab : a≠b) (hca : c≠a) (hcb : c≠b)
    (hout : OutsidePairCharacter Q a b) :
    ∃ ell : Character r,∀ x,root (Q.eval x)=root Q.constant*sign (ell (vectorWord x)) := by
  obtain ⟨he,hz⟩ := even_empty_of_cards h a b c hab hca hcb hout
  obtain ⟨ell,hell⟩ := phase_character_of_even_empty Q he hz
  exact ⟨ell,fun x => by rw [source_phase,hell]⟩

end
end Holant.ReedMuller.CharacterRecognition
