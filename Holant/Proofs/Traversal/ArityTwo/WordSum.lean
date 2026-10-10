import Holant.Proofs.Traversal.ArityTwo.ComponentSum


namespace Holant.LocalDrafts.TraversalCompletion.ArityTwo
open Holant Holant.Complexity PortWalk OrderedDenote
open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false
variable {K : Type} [CommSemiring K]

def pathWordValue (left right : Bool → K) (ms : List (Kernel K)) : List Bool → K
  | [] => 0
  | a::bits => left a * rightValue right ms (a::bits)

def cycleWordValue (ms : List (Kernel K)) : List Bool → K
  | [] => 0
  | a::bits => rightValue (fun _ => 1) ms ((a::bits)++[a])

theorem sum_pathWordValue (left right : Bool → K) (ms : List (Kernel K)) :
    (∑ x : Fin (ms.length+1) → Bool, pathWordValue left right ms (List.ofFn x)) =
      pathValue left ms right := by
  simpa only [List.ofFn_succ,pathWordValue] using sum_path_rightValue ms left right

theorem sum_cycleWordValue (ms : List (Kernel K)) (hn : ms ≠ []) :
    (∑ x : Fin ms.length → Bool, cycleWordValue ms (List.ofFn x)) = cycleValue ms := by
  cases ms with
  | nil => exact (hn rfl).elim
  | cons M ms =>
    have he := sum_cycle_rightValue ms.length (fun i => (M::ms).get i)
    have hg : List.ofFn (fun i : Fin (ms.length+1) => (M::ms).get i) = M::ms := by
      simpa only [List.length_cons] using List.ofFn_get (M::ms)
    rw [hg] at he
    simpa only [List.length_cons,List.ofFn_succ,cycleWordValue] using he

theorem sum_words_congr_length {n m : ℕ} (hn : n = m) (f : List Bool → K) :
    (∑ x : Fin n → Bool, f (List.ofFn x)) = ∑ x : Fin m → Bool, f (List.ofFn x) := by
  cases hn
  rfl

@[simp] theorem realizeMatrix_id (M : Kernel K) : realizeMatrix id M = M := rfl

@[simp] theorem map_realizeMatrix_id (ms : List (Kernel K)) : ms.map (realizeMatrix id) = ms := by
  induction ms <;> simp_all

variable {s b : ℕ} {arity : ℕ → ℕ}
variable (r : RawClosedNetwork) (h : r.WellFormed s b arity)

theorem terminal_word_length {p q : r.Ports arity} {xs : List (r.Ports arity)}
    (ht : Trace r h p xs (.terminal q)) : (portWord r xs).length+1 = 2*xs.length := by
  generalize hs : Stop.terminal q = stop at ht
  induction ht with
  | repeated p => cases hs
  | terminal p ho => simp [portWord,ho]
  | step p out xs stop ho ht ih =>
    have hh := ih hs
    simp [portWord,ho] at *
    omega

theorem repeated_word_length {p q : r.Ports arity} {xs : List (r.Ports arity)}
    (ht : Trace r h p xs (.repeated q)) : (portWord r xs).length = 2*xs.length := by
  generalize hs : Stop.repeated q = stop at ht
  induction ht with
  | terminal p ho => cases hs
  | repeated p => rfl
  | step p out xs stop ho ht ih =>
    have hh := ih hs
    simp [portWord,ho] at *
    omega

noncomputable def wordEquiv (root : Fin r.vertices.length) (word : List (r.Ports arity))
    (hn : word.Nodup)
    (hm : ∀ p, p ∈ word ↔ (r.shape h).componentOf p.1 = Comp r h root) :
    Fin word.length ≃ ((r.shape h).ComponentEdge (Comp r h root) × Bool) :=
  (listFiberEquiv word hn _ hm).trans (componentPortEquiv r h root)

/-- Every slot of the computed port word reads precisely its independent bit. -/
theorem lift_word (root : Fin r.vertices.length) (word : List (r.Ports arity))
    (hn : word.Nodup)
    (hm : ∀ p, p ∈ word ↔ (r.shape h).componentOf p.1 = Comp r h root)
    (bits : Fin word.length → Bool) :
    word.map (liftAssignment r h root
      ((Equiv.arrowCongr (wordEquiv r h root word hn hm) (Equiv.refl Bool)) bits)) = List.ofFn bits := by
  have hi (i : Fin word.length) :
      liftAssignment r h root
        ((Equiv.arrowCongr (wordEquiv r h root word hn hm) (Equiv.refl Bool)) bits) (word.get i) = bits i := by
    rw [liftAssignment,dif_pos ((hm _).mp (List.get_mem word i))]
    change ((Equiv.arrowCongr (wordEquiv r h root word hn hm) (Equiv.refl Bool)) bits)
      (wordEquiv r h root word hn hm i) = bits i
    simp [Equiv.arrowCongr]
  calc
    _ = (List.ofFn word.get).map (liftAssignment r h root
      ((Equiv.arrowCongr (wordEquiv r h root word hn hm) (Equiv.refl Bool)) bits)) :=
      congrArg (List.map _) (List.ofFn_get word).symm
    _ = List.ofFn bits := by
      rw [List.map_ofFn]
      congr 1
      funext i
      exact hi i

end Holant.LocalDrafts.TraversalCompletion.ArityTwo
