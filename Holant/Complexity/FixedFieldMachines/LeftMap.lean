import Holant.Complexity.FixedFieldMachines.Wiring
import Mathlib.Tactic.Linarith

/-! A genuine returning compiler for mapping a finite Boolean-stack machine
under the first component of the explicit pair codec. The entire second word
stays on a separate stack. Input parsing and output serialization are ordinary
counted loops, and all source-machine work stacks are clean on return. -/
namespace Holant.Complexity.FixedFieldMachines
namespace LeftMap
open Turing Computability BinaryCompose StackProtocol Holant.Algebraic
variable (m : Machine)
abbrev Keys := m.K ⊕ Bool
abbrev Labels := m.Label ⊕ Fin 6

def layout (suffix scratch : List Bool) : StackEmbedding m.K (Keys m) where
  key := Sum.inl
  lift tapes := Sum.elim tapes (fun b => if b then scratch else suffix)
  lookup _ _ := rfl
  update tapes k word := by
    funext key
    cases key with
    | inl j => by_cases h : j = k <;> simp [Function.update, h]
    | inr b => simp [Function.update]

def states : StateEmbedding m.State (Option Bool × m.State) where
  put state := (none, state)
  get := Prod.snd
  get_put _ := rfl

private theorem stmt_frame (suffix scratch : List Bool)
    (q : TM2.Stmt (fun _ : m.K => Bool) m.Label m.State) :
    embedStmt (layout m [] []) (states m) Sum.inl (some (.inr (2 : Fin 6))) q =
      embedStmt (layout m suffix scratch) (states m) Sum.inl (some (.inr (2 : Fin 6))) q := by
  induction q <;> simp only [embedStmt, *] <;> rfl

/-- Six administrative labels plus exactly the source machine's labels. -/
def program : Labels m → Stmt (Keys m) (Labels m) m.State
  | .inl l => embedStmt (layout m [] []) (states m) Sum.inl (some (.inr (2 : Fin 6))) (m.program l)
  | .inr l => if l = 0 then GraphPreprocessing.Frame.scanStmt (.inr false) (.inr true) (.inr 0) (.inr 1) (.inr 5)
    else if l = 1 then copyMoveStmt (.inr true) (.inl m.input) (.inr 1) (.inl m.main)
    else if l = 2 then copyMoveStmt (.inl m.output) (.inr true) (.inr 2) (.inr 3)
    else if l = 3 then FrameEmit.delimiterStmt (.inr false) (.inr 4)
    else if l = 4 then FrameEmit.emitStmt (.inr true) (.inr false) (.inr 4) (.inr 5)
    else .halt

abbrev machine : Machine where
  K := Keys m
  input := .inr false
  output := .inr false
  Label := Labels m
  main := .inr 0
  State := Option Bool × m.State
  initial := (none, m.initial)
  program := program m

def tapes (key : m.K) (word suffix scratch : List Bool) : Keys m → List Bool :=
  (layout m suffix scratch).lift (wordTape key word)

theorem tapes_extract (key : m.K) (word suffix scratch : List Bool) :
    tapes m key word suffix scratch = tapes3 (fun _ => []) (.inr false) (.inl key) (.inr true)
      suffix word scratch := by
  funext k
  cases k with
  | inl k => by_cases h : k = key <;> simp [tapes, layout, tapes3, wordTape, Function.update, h]
  | inr b => cases b <;> rfl

theorem tapes_emit (key : m.K) (word suffix scratch : List Bool) :
    tapes m key word suffix scratch = tapes3 (fun _ => []) (.inl key) (.inr false) (.inr true)
      word suffix scratch := by
  funext k
  cases k with
  | inl k => by_cases h : k = key <;> simp [tapes, layout, tapes3, wordTape, Function.update, h]
  | inr b => cases b <;> rfl

private theorem init_cfg (input : List Bool) :
    cfg (.inr 0 : Labels m) m.initial (tapes m m.input [] input []) =
      initList (machine m).computer input := by
  rw [Machine.init_eq]
  congr 1; funext k
  cases k with
  | inl k => simp [tapes, layout, wordTape]
  | inr b => cases b <;> rfl

private theorem embedded_init (input suffix : List Bool) :
    embedCfg (layout m suffix []) (states m) Sum.inl (some (.inr (2 : Fin 6)))
      (initList m.computer input) =
      cfg (.inl m.main : Labels m) m.initial (tapes m m.input input suffix []) := by
  rw [Machine.init_eq]; rfl

private theorem embedded_halt (output suffix : List Bool) :
    embedCfg (layout m suffix []) (states m) Sum.inl (some (.inr (2 : Fin 6)))
      (haltList m.computer output) =
      cfg (.inr 2 : Labels m) m.initial (tapes m m.output output suffix []) := by
  rw [Machine.halt_eq]; rfl

private theorem halt_step (output : List Bool) :
    (machine m).computer.step (cfg (.inr 5 : Labels m) m.initial (tapes m m.output [] output [])) =
      some (haltList (machine m).computer output) := by
  rw [Machine.halt_eq]
  dsimp [FinTM2.step, TM2.step, machine, program, cfg, TM2.stepAux]
  congr 2; funext k
  cases k with
  | inl k => simp [tapes, layout, wordTape]
  | inr b => cases b <;> rfl

/-- Exact operational lifting, including both framed interfaces and final halt. -/
theorem exact_run (input output suffix : List Bool) (n : ℕ)
    (h : (fun p => p.bind m.computer.step)^[n] (some (initList m.computer input)) =
      some (haltList m.computer output)) :
    RunsExactly (machine m).computer.step
      (initList (machine m).computer (frame input ++ suffix))
      (haltList (machine m).computer (frame output ++ suffix))
      (2 * input.length + n + 2 * output.length + 6) := by
  have parse := GraphPreprocessing.Frame.extract_exact (.inr false : Keys m) (.inl m.input) (.inr true)
    (by intro h; cases h) (by simp) (by intro h; cases h)
    (machine m).computer.step (.inr 0 : Labels m) (.inr 1) (.inl m.main) (.inr 5)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) m.initial (fun _ => []) input suffix []
  rw [← tapes_extract, ← tapes_extract] at parse
  simp only [List.append_nil, init_cfg] at parse
  have core := embed_run (layout m suffix []) (states m) Sum.inl (some (.inr (2 : Fin 6)))
    m.program (program m) (fun l => by simpa only [program] using stmt_frame m suffix [] (m.program l))
    (initList m.computer input) (haltList m.computer output) n h
  rw [embedded_init, embedded_halt] at core
  change RunsExactly (machine m).computer.step _ _ n at core
  have emit := FrameEmit.prepend_exact (.inl m.output : Keys m) (.inr false) (.inr true)
    (by intro h; cases h) (by intro h; cases h) (by simp)
    (machine m).computer.step (.inr 2 : Labels m) (.inr 3) (.inr 4) (.inr 5)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl)
    m.initial (fun _ => []) output suffix
  rw [← tapes_emit, ← tapes_emit] at emit
  have run := ((parse.trans core).trans emit).trans (runsExactly_one (halt_step m (frame output ++ suffix)))
  convert run using 1; omega

end LeftMap

open Computability BinaryCompose

/-- Polynomial-time map of the first product component by actual subroutine
embedding. The output-length cost comes from the source program's stack bound. -/
noncomputable def leftMapComputes {α β γ : Type} {ea : Encoding α Bool} {eb : Encoding β Bool}
    (ec : Encoding γ Bool) {f : α → β} (w : Computes ea eb f) :
    Computes (pairEncoding ea ec) (pairEncoding eb ec) (fun p => (f p.1, p.2)) where
  machine := LeftMap.machine w.machine
  time := 4 * Polynomial.X + Polynomial.C (1 + 2 * w.machine.primitiveBudget) * w.time + 6
  outputs p := by
    let h := w.outputs p.1
    refine { steps := 2 * (ea.encode p.1).length + h.steps + 2 * (eb.encode (f p.1)).length + 6
             evals_in_steps := LeftMap.exact_run w.machine _ _ _ h.steps h.evals_in_steps
             steps_le_m := ?_ }
    have hin : (ea.encode p.1).length ≤ ((pairEncoding ea ec).encode p).length := by simp; omega
    have ht := natPolynomial_eval_mono w.time hin
    have hs := h.steps_le_m
    have ho := w.machine.output_length_le _ _ _ h
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X,
      Polynomial.eval_C]
    nlinarith

/-- Mapping the second component uses the proved physical swaps, not a host-word map. -/
noncomputable def rightMapComputes {α β γ : Type} (ea : Encoding α Bool)
    {eb : Encoding β Bool} {ec : Encoding γ Bool} {f : β → γ} (w : Computes eb ec f) :
    Computes (pairEncoding ea eb) (pairEncoding ea ec) (fun p => (p.1, f p.2)) :=
  congrComputes (((Wiring.swapComputes ea eb).andThen (leftMapComputes ea w)).andThen
    (Wiring.swapComputes ec ea)) (fun _ => rfl)

/-- Fanout, two independently compiled computations and a literal paired result. -/
noncomputable def pairComputes {α β γ : Type} {ea : Encoding α Bool}
    {eb : Encoding β Bool} {ec : Encoding γ Bool} {f : α → β} {g : α → γ}
    (u : Computes ea eb f) (v : Computes ea ec g) :
    Computes ea (pairEncoding eb ec) (fun a => (f a, g a)) :=
  congrComputes (((Wiring.diagonalComputes ea).andThen (leftMapComputes ea u)).andThen
    (rightMapComputes eb v)) (fun _ => rfl)

end Holant.Complexity.FixedFieldMachines
