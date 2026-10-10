import Holant.OneHot.StackProgram.Machine.StackWord
import Holant.Complexity.FixedFieldMachines.PairEncoding
import Holant.Complexity.BinaryCompose.Embed

/-!
# A real encoded arithmetic opcode around a finite-machine provider

This compiler accepts an actual clean Boolean-stack machine for the exact wire
protocol `frame(left) ++ right`. It pops two framed value-stack elements, builds
that protocol with bit loops, runs the source machine through structural finite
syntax embedding, and reinserts its encoded result. All worker stacks are empty
on successful return. No semiring operation or word-level callback occurs in
any transition. The runtime explicitly depends on all three fieldword lengths.
-/
set_option backward.isDefEq.respectTransparency false

namespace Holant.OneHot.StackProgram.Machine.Operator
open Turing Computability Holant.Complexity StackProtocol BinaryCompose

variable (m : BinaryCompose.Machine)

abbrev Keys := m.K ⊕ Fin 4
abbrev Labels := m.Label ⊕ Fin 18
abbrev States := Option Bool × m.State
abbrev Config := TM2.Cfg (fun _ : Keys m => Bool) (Labels m) (States m)
abbrev Statement := TM2.Stmt (fun _ : Keys m => Bool) (Labels m) (States m)

def tapes (worker : m.K → List Bool) (data left right scratch : List Bool) : Keys m → List Bool :=
  Sum.elim worker ![data, left, right, scratch]

private theorem tapes_word (word : List Bool) :
    tapes m (fun _ => []) word [] [] [] = wordTape (.inr 0 : Keys m) word := by
  funext k
  cases k with
  | inl k => rfl
  | inr k => fin_cases k <;> rfl

def layout (frame : Fin 4 → List Bool) : StackEmbedding m.K (Keys m) where
  key := Sum.inl
  lift worker := Sum.elim worker frame
  lookup _ _ := rfl
  update worker k word := by
    funext key
    cases key with
    | inl j => by_cases h : j = k <;> simp [Function.update, h, -Sum.elim_update_left,
        -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]
    | inr j => simp [Function.update, -Sum.elim_update_left,
        -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]

def states : StateEmbedding m.State (States m) where
  put v := (none, v)
  get v := v.2
  get_put _ := rfl

/-- The tape-frame specification never enters the generated instructions. -/
theorem embed_frame (frame other : Fin 4 → List Bool)
    (q : TM2.Stmt (fun _ : m.K => Bool) m.Label m.State) :
    embedStmt (layout m frame) (states m) (Sum.inl : m.Label → Labels m) (some (.inr 11)) q =
      embedStmt (layout m other) (states m) (Sum.inl : m.Label → Labels m) (some (.inr 11)) q := by
  induction q <;> simp [embedStmt, *] <;> rfl

def program : Labels m → Statement m
  | .inl label => embedStmt (layout m (fun _ => [])) (states m) Sum.inl (some (.inr 11)) (m.program label)
  | .inr label =>
    if label = 0 then StackWord.markerStmt (.inr 0) (.inr 1) (.inr 16) (.inr 17)
    else if label = 1 then GraphPreprocessing.Frame.scanStmt (.inr 0) (.inr 3) (.inr 1) (.inr 2) (.inr 17)
    else if label = 2 then copyMoveStmt (.inr 3) (.inr 1) (.inr 2) (.inr 3)
    else if label = 3 then StackWord.markerStmt (.inr 0) (.inr 4) (.inr 16) (.inr 17)
    else if label = 4 then GraphPreprocessing.Frame.scanStmt (.inr 0) (.inr 3) (.inr 4) (.inr 5) (.inr 17)
    else if label = 5 then copyMoveStmt (.inr 3) (.inr 2) (.inr 5) (.inr 6)
    else if label = 6 then copyMoveStmt (.inr 1) (.inr 3) (.inr 6) (.inr 7)
    else if label = 7 then FixedFieldMachines.FrameEmit.delimiterStmt (.inr 2) (.inr 8)
    else if label = 8 then FixedFieldMachines.FrameEmit.emitStmt (.inr 3) (.inr 2) (.inr 8) (.inr 9)
    else if label = 9 then copyMoveStmt (.inr 2) (.inr 3) (.inr 9) (.inr 10)
    else if label = 10 then copyMoveStmt (.inr 3) (.inl m.input) (.inr 10) (.inl m.main)
    else if label = 11 then copyMoveStmt (.inl m.output) (.inr 3) (.inr 11) (.inr 12)
    else if label = 12 then FixedFieldMachines.FrameEmit.delimiterStmt (.inr 0) (.inr 13)
    else if label = 13 then FixedFieldMachines.FrameEmit.emitStmt (.inr 3) (.inr 0) (.inr 13) (.inr 14)
    else if label = 14 then StackWord.consStmt (.inr 0) (.inr 15)
    else .halt

/-- The integrated arithmetic opcode is itself a finite, uniformly Boolean TM2. -/
abbrev machine : BinaryCompose.Machine where
  K := Keys m
  input := .inr 0
  output := .inr 0
  Label := Labels m
  main := .inr 0
  State := States m
  initial := (none, m.initial)
  program := program m

private theorem pop_left (x y : List Bool) :
    RunsExactly (machine m).computer.step
      (cfg (.inr 0) m.initial (tapes m (fun _ => []) (true :: Holant.Algebraic.frame x ++ y) [] [] []))
      (cfg (.inr 3) m.initial (tapes m (fun _ => []) y x [] [])) (2 * x.length + 3) := by
  have h := StackWord.pop_exact (.inr 0 : Keys m) (.inr 1) (.inr 3)
    (by simp) (by simp) (by simp) (machine m).computer.step
    (.inr 0) (.inr 1) (.inr 2) (.inr 3) (.inr 16) (.inr 17)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl)
    m.initial (fun _ => []) x y []
  simp only [List.append_nil] at h
  convert h using 1 <;> congr 1 <;> funext k <;> cases k with
  | inl k => rfl
  | inr k => fin_cases k <;> rfl

private theorem pop_right (x y tail : List Bool) :
    RunsExactly (machine m).computer.step
      (cfg (.inr 3) m.initial (tapes m (fun _ => []) (true :: Holant.Algebraic.frame y ++ tail) x [] []))
      (cfg (.inr 6) m.initial (tapes m (fun _ => []) tail x y [])) (2 * y.length + 3) := by
  have h := StackWord.pop_exact (.inr 0 : Keys m) (.inr 2) (.inr 3)
    (by simp) (by simp) (by simp) (machine m).computer.step
    (.inr 3) (.inr 4) (.inr 5) (.inr 6) (.inr 16) (.inr 17)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl)
    m.initial (tapes m (fun _ => []) [] x [] []) y tail []
  simp only [List.append_nil] at h
  convert h using 1 <;> congr 1 <;> funext k <;> cases k with
  | inl k => rfl
  | inr k => fin_cases k <;> rfl

private theorem make_pair (x y tail : List Bool) :
    RunsExactly (machine m).computer.step
      (cfg (.inr 6) m.initial (tapes m (fun _ => []) tail x y []))
      (cfg (.inr 9) m.initial (tapes m (fun _ => []) tail [] (Holant.Algebraic.frame x ++ y) []))
      (2 * x.length + 3) := by
  have h := FixedFieldMachines.FrameEmit.prepend_exact (.inr 1 : Keys m) (.inr 2) (.inr 3)
    (by simp) (by simp) (by simp) (machine m).computer.step
    (.inr 6) (.inr 7) (.inr 8) (.inr 9)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl)
    m.initial (tapes m (fun _ => []) tail [] [] []) x y
  convert h using 1 <;> congr 1 <;> funext k <;> cases k with
  | inl k => rfl
  | inr k => fin_cases k <;> rfl

private theorem load_pair (word tail : List Bool) :
    RunsExactly (machine m).computer.step
      (cfg (.inr 9) m.initial (tapes m (fun _ => []) tail [] word []))
      (cfg (.inl m.main) m.initial (tapes m (wordTape m.input word) tail [] [] []))
      (2 * (word.length + 1)) := by
  have h := StackWord.move_exact (.inr 2 : Keys m) (.inl m.input) (.inr 3)
    (by intro h; cases h) (by simp) (by intro h; cases h) (machine m).computer.step
    (.inr 9) (.inr 10) (.inl m.main)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl)
    m.initial (tapes m (fun _ => []) tail [] [] []) word []
  simp only [List.append_nil] at h
  convert h using 1 <;> congr 1 <;> funext k <;> cases k with
  | inl k => simp [tapes, tapes3, wordTape, Function.update]
  | inr k => fin_cases k <;> rfl

/-- Source transitions preserve the surrounding value-stack suffix verbatim. -/
theorem provider_run (input output tail : List Bool) (time : ℕ)
    (h : (fun c => c.bind m.computer.step)^[time] (some (initList m.computer input)) =
      some (haltList m.computer output)) :
    RunsExactly (machine m).computer.step
      (cfg (.inl m.main) m.initial (tapes m (wordTape m.input input) tail [] [] []))
      (cfg (.inr 11) m.initial (tapes m (wordTape m.output output) tail [] [] [])) time := by
  have run := embed_run (layout m ![tail, [], [], []]) (states m)
    (Sum.inl : m.Label → Labels m) (some (.inr 11)) m.program (program m)
    (by
      intro label
      change embedStmt _ _ _ _ _ = _
      exact embed_frame m (fun _ => []) ![tail, [], [], []] (m.program label))
    (initList m.computer input) (haltList m.computer output) time h
  rw [BinaryCompose.Machine.init_eq, BinaryCompose.Machine.halt_eq] at run
  exact run

private theorem push_result (word tail : List Bool) :
    RunsExactly (machine m).computer.step
      (cfg (.inr 11) m.initial (tapes m (wordTape m.output word) tail [] [] []))
      (cfg (.inr 15) m.initial (tapes m (fun _ => [])
        (true :: Holant.Algebraic.frame word ++ tail) [] [] [])) (2 * word.length + 4) := by
  have h := StackWord.push_exact (.inl m.output : Keys m) (.inr 0) (.inr 3)
    (by intro h; cases h) (by intro h; cases h) (by simp) (machine m).computer.step
    (.inr 11) (.inr 12) (.inr 13) (.inr 14) (.inr 15)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl)
    m.initial (tapes m (fun _ => []) [] [] [] []) word tail
  convert h using 1 <;> congr 1 <;> funext k <;> cases k with
  | inl k => simp [tapes, tapes3, wordTape, Function.update]
  | inr k => fin_cases k <;> rfl

/-- All loader, operand framing, provider, transfer and cleanup transitions. -/
theorem run_exact (x y z tail : List Bool) (time : ℕ)
    (h : (fun c => c.bind m.computer.step)^[time]
      (some (initList m.computer (Holant.Algebraic.frame x ++ y))) =
      some (haltList m.computer z)) :
    RunsExactly (machine m).computer.step
      (initList (machine m).computer
        (true :: Holant.Algebraic.frame x ++ (true :: Holant.Algebraic.frame y ++ tail)))
      (haltList (machine m).computer (true :: Holant.Algebraic.frame z ++ tail))
      (8 * x.length + 4 * y.length + 2 * z.length + time + 18) := by
  have first := pop_left m x (true :: Holant.Algebraic.frame y ++ tail)
  have a := first.trans (pop_right m x y tail)
  have b := a.trans (make_pair m x y tail)
  have c := b.trans (load_pair m (Holant.Algebraic.frame x ++ y) tail)
  have d := c.trans (provider_run m _ _ tail time h)
  have e := d.trans (push_result m z tail)
  have last : (machine m).computer.step
      (cfg (.inr 15) m.initial (tapes m (fun _ => [])
        (true :: Holant.Algebraic.frame z ++ tail) [] [] [])) =
      some (haltList (machine m).computer (true :: Holant.Algebraic.frame z ++ tail)) := by
    rw [BinaryCompose.Machine.halt_eq]
    change some (⟨none, (none, m.initial),
      tapes m (fun _ => []) (true :: Holant.Algebraic.frame z ++ tail) [] [] []⟩ : Config m) = _
    rw [tapes_word]
  have all := e.trans (runsExactly_one last)
  rw [BinaryCompose.Machine.init_eq]
  change RunsExactly _ (cfg (Sum.inr 0 : Labels m) m.initial
    (wordTape (.inr 0 : Keys m)
      (true :: Holant.Algebraic.frame x ++ (true :: Holant.Algebraic.frame y ++ tail)))) _ _
  rw [← tapes_word]
  convert all using 1
  simp only [List.length_append, Holant.Algebraic.frame_length]
  omega

/-- Instantiate the opcode with an actual exact-codec finite-machine provider.
The runtime is parameterized by a proved bound on BOTH operands and the result. -/
def provider_timed {V : Type} (e : Encoding V Bool) (f : V × V → V)
    (w : BinaryCompose.Computes (FixedFieldMachines.pairEncoding e e) e f)
    (x y : V) (tail : List V) (W : ℕ)
    (hx : (e.encode x).length ≤ W) (hy : (e.encode y).length ≤ W)
    (hz : (e.encode (f (x, y))).length ≤ W) :
    TM2OutputsInTime (machine w.machine).computer
      ((stackEncoding e).encode (x :: y :: tail))
      (some ((stackEncoding e).encode (f (x, y) :: tail)))
      (w.time.eval (3 * W + 1) + 14 * W + 18) := by
  let h := w.outputs (x, y)
  refine { steps := 8 * (e.encode x).length + 4 * (e.encode y).length +
      2 * (e.encode (f (x, y))).length + h.steps + 18
           evals_in_steps := ?_
           steps_le_m := ?_ }
  · have hr := run_exact w.machine (e.encode x) (e.encode y) (e.encode (f (x, y)))
      ((stackEncoding e).encode tail) h.steps h.evals_in_steps
    simpa only [stackEncoding, framedListEncoding, framedListEncode,
      List.cons_append, Option.map_some, RunsExactly.toTimed, FinTM2.Cfg,
      BinaryCompose.Machine.computer, machine, Keys, Labels, States, StackProtocol.Cfg]
      using hr.toTimed.evals_in_steps
  · have ht := h.steps_le_m
    have hi : ((FixedFieldMachines.pairEncoding e e).encode (x, y)).length ≤ 3 * W + 1 := by
      simp only [FixedFieldMachines.pairEncoding_length]
      omega
    have hp := natPolynomial_eval_mono w.time hi
    omega

/-- A provider carries real finite programs and their clean timed simulations.
These are obligations for fixed-field arithmetic, not unit-cost callbacks. -/
structure Providers {V : Type} [CommSemiring V] (e : Encoding V Bool) where
  add : BinaryCompose.Computes (FixedFieldMachines.pairEncoding e e) e
    (fun p => p.1 + p.2)
  mul : BinaryCompose.Computes (FixedFieldMachines.pairEncoding e e) e
    (fun p => p.1 * p.2)

end Holant.OneHot.StackProgram.Machine.Operator
