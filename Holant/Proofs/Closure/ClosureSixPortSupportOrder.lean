import Holant.Proofs.Closure.ClosureSixPortSelection

/-! NEW UNVERIFIED actual ordered contraction witnesses from the normalized
support table. Both deleted coordinates and every surviving port are literal. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSixPort
open Holant

def pairOrder (i j : Fin 6) : Equiv.Perm (Fin 6) :=
  (Equiv.swap 1 ((Equiv.swap 0 i) j)).trans (Equiv.swap 0 i)

theorem pairOrder_first (i j : Fin 6) (distinct : i ≠ j) : pairOrder i j 0 = i := by
  fin_cases i <;> fin_cases j <;> simp_all [pairOrder,Equiv.trans_apply,Equiv.swap_apply_def]

theorem pairOrder_second (i j : Fin 6) (distinct : i ≠ j) : pairOrder i j 1 = j := by
  fin_cases i <;> fin_cases j <;> simp_all [pairOrder,Equiv.trans_apply,Equiv.swap_apply_def]

theorem residualSix_eq_remaining (e : Equiv.Perm (Fin 6)) (x y : Word 6)
    (same : residualSix e x = residualSix e y) (r : Fin 6)
    (first : r ≠ e 0) (second : r ≠ e 1) : x r = y r := by
  obtain ⟨j,rfl⟩ := e.surjective r
  fin_cases j
  · exact (first rfl).elim
  · exact (second rfl).elim
  · exact congrFun same (0 : Fin 4)
  · exact congrFun same (1 : Fin 4)
  · exact congrFun same (2 : Fin 4)
  · exact congrFun same (3 : Fin 4)

/-- The table chooses an actual ordered pair and kernel parity. Its SAME
selected support has six/eight words and each output has a unique lift. -/
theorem normalized_projection_choice (edge : Fin 6) (a b o : Bool)
    (notMatching : ¬ (edge=0 ∧ a=false ∧ b=true)) :
    ∃ e : Equiv.Perm (Fin 6), ∃ p : Bool,
      Set.InjOn (residualSix e) {w | w ∈ selectedWords (flatSupport edge a b o) e p} ∧
      ((selectedWords (flatSupport edge a b o) e p).card=6 ∨
        (selectedWords (flatSupport edge a b o) e p).card=8) := by
  have atlas := canonical_four_flat_atlas edge a b o
  have good := atlas.resolve_left (fun h => notMatching ⟨h.1,h.2.1,h.2.2.1⟩)
  let key := projectionWitness edge a b o
  let e := pairOrder key.1 key.2.1
  have first : e 0 = key.1 := pairOrder_first _ _ good.1
  have second : e 1 = key.2.1 := pairOrder_second _ _ good.1
  have selected : selectedWords (flatSupport edge a b o) e key.2.2 = selectedSupport edge a b o := by
    unfold selectedWords selectedSupport
    rw [first,second]

  refine ⟨e,key.2.2,?_,by rw [selected]; exact good.2.2⟩
  simp only [selectedWords,flatSupport]
  apply selectedImage_injOn
  intro v hv w hw hxp hyp same
  apply good.2.1 v.1 v.2.1 v.2.2 w.1 w.2.1 w.2.2
  · simpa only [first,second,key] using hxp
  · simpa only [first,second,key] using hyp
  · intro r hr0 hr1
    apply residualSix_eq_remaining e _ _ same r
    · simpa only [first] using hr0
    · simpa only [second] using hr1

/-- The selected ACTUAL phase-one card has exactly six/eight nonzero entries.
Nonzero coefficients are preserved by unique lifts, not by an assumed generic
noncancellation condition. -/
theorem normalized_actual_card_support (edge : Fin 6) (a b o : Bool)
    (notMatching : ¬ (edge=0 ∧ a=false ∧ b=true))
    (h : Signature ℂ 6) (support : ∀ w, h w ≠ 0 ↔ w ∈ flatSupport edge a b o) :
    ∃ e : Equiv.Perm (Fin 6), ∃ p : Bool,
      ∃ T : Finset (Word 4),
      (T.card=6 ∨ T.card=8) ∧ (∀ x, phaseCard h e p 1 x ≠ 0 ↔ x ∈ T) := by
  obtain ⟨e,p,injective,card⟩ := normalized_projection_choice edge a b o notMatching
  refine ⟨e,p,selectedOutputs (flatSupport edge a b o) e p,?_,?_⟩
  · rw [selectedOutputs_card _ e p injective]
    exact card
  · exact phase_one_support h _ support e p injective

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSixPort
