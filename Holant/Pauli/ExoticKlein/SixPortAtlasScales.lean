import Holant.Pauli.ExoticKlein.SixPortAtlasClassification

/-! The manuscript's exact five direction triples and signed half-scale
lines, with actual card nonvanishing and the1+16histogram proved. -/
namespace Holant.Pauli.ExoticKlein.SixPort.Atlas
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators

def fourStates : Fin 4 → DirectionTriple :=
  ![![some (directionEquiv 1),some (directionEquiv 2),some (directionEquiv 3)],
    ![some (directionEquiv 1),some (directionEquiv 3),some (directionEquiv 2)],
    ![some (directionEquiv 4),some (directionEquiv 8),some (directionEquiv 12)],
    ![some (directionEquiv 4),some (directionEquiv 12),some (directionEquiv 8)]]

def signInt (b : Bool) : ℤ := if b then 1 else -1
def sign (b : Bool) : ℂ := if b then 1 else -1

def scalePattern (eps delta : Bool) : Fin 4 → ℂ :=
  ![1,sign eps,sign delta/2,sign eps*sign delta/2]

def scalePattern2 (eps delta : Bool) : Fin 4 → ℤ :=
  ![2,2*signInt eps,signInt delta,signInt eps*signInt delta]

def signSlot (g : Fin 4) (eps delta : Bool) : Fin 17 :=
  ![if eps then (if delta then 14 else 13) else (if delta then 16 else 15),
    if eps then (if delta then 9 else 10) else (if delta then 11 else 12),
    if eps then (if delta then 6 else 5) else (if delta then 8 else 7),
    if eps then (if delta then 1 else 2) else (if delta then 3 else 4)] g

def slotMap : (Unit ⊕ (Fin 4 × Bool × Bool)) → Fin 17 :=
  Sum.elim (fun _ => 0) (fun s => signSlot s.1 s.2.1 s.2.2)

theorem slotMap_bijective : Function.Bijective slotMap := by decide +kernel

def slotEquiv : (Unit ⊕ (Fin 4 × Bool × Bool)) ≃ Fin 17 :=
  Equiv.ofBijective slotMap slotMap_bijective

theorem state_signSlot (g : Fin 4) (eps delta : Bool) :
    candidateState (signSlot g eps delta) = fourStates g := by
  revert g eps delta
  decide +kernel

theorem scale2_signSlot (g : Fin 4) (eps delta : Bool) :
    candidateScale2 (signSlot g eps delta) = scalePattern2 eps delta := by
  revert g eps delta
  decide +kernel

theorem scale_signSlot (g : Fin 4) (eps delta : Bool) :
    candidateScale (signSlot g eps delta) = scalePattern eps delta := by
  funext a
  unfold candidateScale
  rw [scale2_signSlot]
  fin_cases a <;> cases eps <;> cases delta <;> norm_num [scalePattern2,scalePattern,signInt,sign]

def singleTensor : Signature ℂ 6 := normalizedTensor (fun _ => none) ![1,0,0,0]
def signedTensor (g : Fin 4) (eps delta : Bool) : Signature ℂ 6 :=
  normalizedTensor (fourStates g) (scalePattern eps delta)

theorem candidate_zero : candidate 0 = singleTensor := by
  rw [candidate_reconstruction]
  have hscale : candidateScale 0 = ![1,0,0,0] := by
    funext a
    fin_cases a <;> norm_num [candidateScale,candidateScale2]
  rw [hscale]
  rfl

theorem candidate_signSlot (g : Fin 4) (eps delta : Bool) :
    candidate (signSlot g eps delta) = signedTensor g eps delta := by
  rw [candidate_reconstruction,state_signSlot,scale_signSlot]
  rfl

/-- Exactly the displayed singleton line and four signed lines on each of
the four displayed nonzero direction triples. -/
theorem normalized_safe_explicit_iff (h : Signature ℂ 6) :
    NormalizedSafe h ↔ h = singleTensor ∨
      ∃ g : Fin 4, ∃ eps delta : Bool, h = signedTensor g eps delta := by
  rw [normalized_safe_iff]
  constructor
  · rintro ⟨i,rfl⟩
    obtain ⟨s,rfl⟩ := slotEquiv.surjective i
    cases s with
    | inl u => exact Or.inl candidate_zero
    | inr s => exact Or.inr ⟨s.1,s.2.1,s.2.2,candidate_signSlot _ _ _⟩
  · rintro (he | ⟨g,eps,delta,he⟩)
    · exact ⟨0,he.trans candidate_zero.symm⟩
    · exact ⟨signSlot g eps delta,he.trans (candidate_signSlot _ _ _).symm⟩

theorem candidateScale_zero_iff (i : Fin 17) (a : Fin 4) :
    candidateScale i a = 0 ↔ candidateScale2 i a = 0 := by
  simp [candidateScale]

theorem direction_scale_zero_iff (d : Direction) (c : ℂ) :
    (fun x => c*directionTensor d x) = 0 ↔ c = 0 := by
  constructor
  · intro hz
    by_contra hc
    have hn := MatchingCard.scaled_matching_ne_zero (fourMatching d.1) ![d.2.1,d.2.2] c hc
    rw [directionTensor_matching] at hz
    exact hn hz
  · intro hc
    subst c
    funext x
    simp

theorem data_live_iff (i : Fin 17) (a : Fin 4) :
    (cardDirections (candidateState i) a).isSome = true ↔ candidateScale2 i a ≠ 0 := by
  revert i a
  decide +kernel

/-- The integer scale table records exactly the ACTUAL zero dual cards. -/
theorem candidate_card_zero_iff (i : Fin 17) (a : Fin 4) :
    baseCard (labelEquiv a) (candidate i) = 0 ↔ candidateScale2 i a = 0 := by
  rw [candidate_reconstruction,baseCard_normalizedTensor]
  cases hd : cardDirections (candidateState i) a with
  | none =>
    have hz := data_live_iff i a
    simp only [hd,Option.isSome_none,Bool.false_eq_true,false_iff,not_not] at hz
    simp only [optionDirection,optionDirectionOver,Pi.zero_apply,mul_zero,hz]
    exact ⟨fun _ => True.intro,fun _ => rfl⟩
  | some d =>
    change (fun x => candidateScale i a*directionTensor d x) = 0 ↔ _
    rw [direction_scale_zero_iff,candidateScale_zero_iff]

def liveCards (i : Fin 17) : Finset (Fin 4) := Finset.univ.filter (fun a => candidateScale2 i a ≠ 0)

theorem mem_liveCards_iff (i : Fin 17) (a : Fin 4) :
    a ∈ liveCards i ↔ baseCard (labelEquiv a) (candidate i) ≠ 0 := by
  simp only [liveCards,Finset.mem_filter,Finset.mem_univ,true_and]
  exact (not_congr (candidate_card_zero_iff i a)).symm

theorem one_card_line_count : (Finset.univ.filter (fun i : Fin 17 => (liveCards i).card = 1)).card = 1 := by
  decide +kernel

theorem four_card_line_count : (Finset.univ.filter (fun i : Fin 17 => (liveCards i).card = 4)).card = 16 := by
  decide +kernel

end
end Holant.Pauli.ExoticKlein.SixPort.Atlas
