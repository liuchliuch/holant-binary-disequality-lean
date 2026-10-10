import Holant.Pauli.ExoticKlein.SixPortBaseSwap
import Holant.Pauli.ExoticKlein.SixPortAnchorData

namespace Holant.Pauli.ExoticKlein.SixPort
noncomputable section

def anchorRepresentative (a : Fin 2222) : Fin 4045 := Fin.ofNat 4045 (anchorRepresentativeData.get a.val)

def baseSwapTags (state : TagState) : TagState := ![state 0,state 2,state 1]

theorem baseSwapTags_semantics (state : TagState) :
    decodeTags (baseSwapTags state) = baseSwapState (decodeTags state) := by
  funext i
  fin_cases i <;> rfl

abbrev AnchorWitness := Nat × Nat × Bool

def anchorWitnessCheck (r : Fin 4045) (w : AnchorWitness) : Bool :=
  decide (wordTags (orbitWord (Fin.ofNat 64 w.2.1))
    (if w.2.2 then baseSwapTags (tagStateEquiv (representativeCode r))
     else tagStateEquiv (representativeCode r)) =
    tagStateEquiv (representativeCode (anchorRepresentative (Fin.ofNat 2222 w.1))))

theorem anchorWitness_sound (r : Fin 4045) (w : AnchorWitness)
    (hc : anchorWitnessCheck r w = true)
    (hs : Solved (stateEquiv (representativeCode (anchorRepresentative (Fin.ofNat 2222 w.1))))) :
    Solved (stateEquiv (representativeCode r)) := by
  have he := congrArg decodeTags (of_decide_eq_true hc)
  rw [wordTags_semantics] at he
  cases hb : w.2.2
  · simp only [hb,Bool.false_eq_true,ite_false] at he
    exact solved_of_word_representative _ _ _ he hs
  · simp only [hb,ite_true,baseSwapTags_semantics] at he
    apply solved_of_baseSwap
    exact solved_of_word_representative _ _ _ he hs

def anchorSource (block : Fin 64) (i : Fin 64) : Fin 4045 := Fin.ofNat 4045 (64*block.val+i.val)

def anchorBlockCheck (block : Fin 64) (data : FiniteTable AnchorWitness) : Bool :=
  decide (∀ i : Fin 64, anchorWitnessCheck (anchorSource block i) (data.get i.val) = true)

theorem anchorBlock_sound (block : Fin 64) (data : FiniteTable AnchorWitness)
    (hc : anchorBlockCheck block data = true)
    (hs : ∀ a, Solved (stateEquiv (representativeCode (anchorRepresentative a)))) (i : Fin 64) :
    Solved (stateEquiv (representativeCode (anchorSource block i))) :=
  anchorWitness_sound _ _ ((of_decide_eq_true hc) i) (hs _)

theorem all_representatives_of_anchors (data : Fin 64 → FiniteTable AnchorWitness)
    (hc : ∀ b, anchorBlockCheck b (data b) = true)
    (hs : ∀ a, Solved (stateEquiv (representativeCode (anchorRepresentative a)))) :
    ∀ r, Solved (stateEquiv (representativeCode r)) := by
  intro r
  let b : Fin 64 := ⟨r.val/64,by have := r.isLt; omega⟩
  let i : Fin 64 := ⟨r.val%64,Nat.mod_lt _ (by decide)⟩
  have he : anchorSource b i = r := by
    apply Fin.ext
    change (64*(r.val/64)+r.val%64)%4045 = r.val
    have hh : 64*(r.val/64)+r.val%64 = r.val := by omega
    rw [hh,Nat.mod_eq_of_lt r.isLt]
  simpa only [he] using anchorBlock_sound b (data b) (hc b) hs i

end
end Holant.Pauli.ExoticKlein.SixPort
