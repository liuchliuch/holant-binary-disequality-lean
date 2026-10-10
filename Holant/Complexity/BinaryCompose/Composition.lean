import Holant.Complexity.BinaryCompose.Embed
import Holant.Complexity.BinaryCompose.Transfer

/-!
# Operational sequential composition of finite Boolean-stack machines

The component stack spaces are disjoint. The first clean output is consumed into
one fresh temporary stack, then consumed again into the second input stack.
This preserves the word's order and leaves all first-machine and temporary
stacks empty. Component input/output aliasing is unrestricted. The two empty
checks cost two transitions; all per-symbol scratch resets occur in the displayed
finite instructions and their costs are included.
-/

namespace Holant.Complexity.BinaryCompose
open Turing Computability

namespace Machine
variable (a b : Machine)

abbrev Keys := a.K ⊕ (b.K ⊕ Unit)
abbrev Labels := a.Label ⊕ (b.Label ⊕ Bool)
abbrev States := Option Bool × (a.State × b.State)
abbrev Configs := TM2.Cfg (fun _ : Keys a b => Bool) (Labels a b) (States a b)
abbrev Statements := TM2.Stmt (fun _ : Keys a b => Bool) (Labels a b) (States a b)

def leftLayout : StackEmbedding a.K (Keys a b) where
  key := Sum.inl
  lift tapes := Sum.elim tapes (fun _ => [])
  lookup _ _ := rfl
  update tapes k word := by
    funext key
    cases key with
    | inl i => by_cases h : i = k <;> simp [Function.update, h, -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]
    | inr j => simp [Function.update, -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]

def rightLayout : StackEmbedding b.K (Keys a b) where
  key k := .inr (.inl k)
  lift tapes := Sum.elim (fun _ => []) (Sum.elim tapes (fun _ => []))
  lookup _ _ := rfl
  update tapes k word := by
    funext key
    cases key with
    | inl i => simp [Function.update, -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]
    | inr j =>
      cases j with
      | inl i => by_cases h : i = k <;> simp [Function.update, h, -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]
      | inr u => simp [Function.update, -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]

def leftStates : StateEmbedding a.State (States a b) where
  put v := (none, v, b.initial)
  get v := v.2.1
  get_put _ := rfl

def rightStates : StateEmbedding b.State (States a b) where
  put v := (none, a.initial, v)
  get v := v.2.2
  get_put _ := rfl

def firstLabel (l : a.Label) : Labels a b := .inl l
def secondLabel (l : b.Label) : Labels a b := .inr (.inl l)
def moveLabel : Labels a b := .inr (.inr false)
def restoreLabel : Labels a b := .inr (.inr true)
def sourceKey : Keys a b := .inl a.output
def destinationKey : Keys a b := .inr (.inl b.input)
def temporaryKey : Keys a b := .inr (.inr ())

/-- Two structurally compiled programs and two finite transfer instructions. -/
def composeProgram : Labels a b → Statements a b
  | .inl label => embedStmt (leftLayout a b) (leftStates a b) (firstLabel a b)
      (some (moveLabel a b)) (a.program label)
  | .inr (.inl label) => embedStmt (rightLayout a b) (rightStates a b) (secondLabel a b)
      none (b.program label)
  | .inr (.inr false) => StackProtocol.copyMoveStmt (sourceKey a b) (temporaryKey a b)
      (moveLabel a b) (restoreLabel a b)
  | .inr (.inr true) => StackProtocol.copyMoveStmt (temporaryKey a b) (destinationKey a b)
      (restoreLabel a b) (secondLabel a b b.main)

/-- The composed ordinary finite Boolean-stack machine. -/
abbrev compose : Machine where
  K := Keys a b
  input := .inl a.input
  output := .inr (.inl b.output)
  Label := Labels a b
  main := firstLabel a b a.main
  State := States a b
  initial := (none, a.initial, b.initial)
  program := composeProgram a b

def leftCfg (c : a.Config) : Configs a b :=
  embedCfg (leftLayout a b) (leftStates a b) (firstLabel a b) (some (moveLabel a b)) c

def rightCfg (c : b.Config) : Configs a b :=
  embedCfg (rightLayout a b) (rightStates a b) (secondLabel a b) none c

@[simp] theorem left_wordTape (key : a.K) (word : List Bool) :
    (leftLayout a b).lift (wordTape key word) = wordTape (.inl key : Keys a b) word := by
  funext k
  cases k with
  | inl k => by_cases h : k = key <;> simp [leftLayout, wordTape, h]
  | inr k => simp [leftLayout, wordTape]

@[simp] theorem right_wordTape (key : b.K) (word : List Bool) :
    (rightLayout a b).lift (wordTape key word) =
      wordTape (.inr (.inl key) : Keys a b) word := by
  funext k
  cases k with
  | inl k => simp [rightLayout, wordTape]
  | inr k =>
    cases k with
    | inl k => by_cases h : k = key <;> simp [rightLayout, wordTape, h]
    | inr k => simp [rightLayout, wordTape]

theorem left_init (input : List Bool) :
    leftCfg a b (initList a.computer input) = initList (compose a b).computer input := by
  rw [init_eq, init_eq]
  simp [leftCfg, embedCfg, leftStates, compose, left_wordTape]

theorem left_halt (word : List Bool) :
    leftCfg a b (haltList a.computer word) =
      StackProtocol.cfg (moveLabel a b) (a.initial, b.initial) (wordTape (sourceKey a b) word) := by
  rw [halt_eq]
  simp [leftCfg, embedCfg, leftStates, StackProtocol.cfg, sourceKey]

theorem right_init (word : List Bool) :
    rightCfg a b (initList b.computer word) =
      StackProtocol.cfg (secondLabel a b b.main) (a.initial, b.initial)
        (wordTape (destinationKey a b) word) := by
  rw [init_eq]
  simp [rightCfg, embedCfg, rightStates, StackProtocol.cfg, destinationKey]

theorem right_halt (word : List Bool) :
    rightCfg a b (haltList b.computer word) = haltList (compose a b).computer word := by
  rw [halt_eq, halt_eq]
  simp [rightCfg, embedCfg, rightStates, compose]

/-- Component runs are preserved one transition for one transition. -/
theorem left_run (c d : a.Config) (n : ℕ)
    (h : (fun p => p.bind a.computer.step)^[n] (some c) = some d) :
    (fun p => p.bind (compose a b).computer.step)^[n] (some (leftCfg a b c)) =
      some (leftCfg a b d) :=
  embed_run (leftLayout a b) (leftStates a b) (firstLabel a b) (some (moveLabel a b))
    a.program (composeProgram a b) (fun _ => rfl) c d n h

theorem right_run (c d : b.Config) (n : ℕ)
    (h : (fun p => p.bind b.computer.step)^[n] (some c) = some d) :
    (fun p => p.bind (compose a b).computer.step)^[n] (some (rightCfg a b c)) =
      some (rightCfg a b d) :=
  embed_run (rightLayout a b) (rightStates a b) (secondLabel a b) none
    b.program (composeProgram a b) (fun _ => rfl) c d n h

/-- The bridge consumes the first output and establishes exactly the second
machine's standard initialization, with all other tapes empty. -/
theorem transfer_run (word : List Bool) :
    (fun p => p.bind (compose a b).computer.step)^[2 * (word.length + 1)]
      (some (leftCfg a b (haltList a.computer word))) =
      some (rightCfg a b (initList b.computer word)) := by
  rw [left_halt, right_init]
  exact transfer_exact (compose a b).computer.step
    (sourceKey a b) (destinationKey a b) (temporaryKey a b)
    (by intro h; cases h) (by intro h; cases h)
    (by intro h; cases h)
    (moveLabel a b) (restoreLabel a b) (secondLabel a b b.main)
    (StackProtocol.executesAt_tm2 _ _ _ rfl) (StackProtocol.executesAt_tm2 _ _ _ rfl)
    (a.initial, b.initial) word

/-- Exact transition-count composition; the first output length is charged. -/
theorem compose_run (input middle output : List Bool) (n m : ℕ)
    (ha : (fun p => p.bind a.computer.step)^[n] (some (initList a.computer input)) =
      some (haltList a.computer middle))
    (hb : (fun p => p.bind b.computer.step)^[m] (some (initList b.computer middle)) =
      some (haltList b.computer output)) :
    (fun p => p.bind (compose a b).computer.step)^[m + (2 * (middle.length + 1) + n)]
      (some (initList (compose a b).computer input)) =
      some (haltList (compose a b).computer output) := by
  have first := left_run a b _ _ n ha
  have last := right_run a b _ _ m hb
  rw [left_init] at first
  rw [right_halt] at last
  rw [Function.iterate_add_apply, Function.iterate_add_apply]
  exact (congrArg (fun state =>
    (fun p => p.bind (compose a b).computer.step)^[m]
      ((fun p => p.bind (compose a b).computer.step)^[2 * (middle.length + 1)] state)) first).trans
    ((congrArg ((fun p => p.bind (compose a b).computer.step)^[m])
      (transfer_run a b middle)).trans last)

/-- Standard clean timed output correctness for the integrated machine. -/
def compose_correct (input middle output : List Bool) (n m : ℕ)
    (ha : TM2OutputsInTime a.computer input (some middle) n)
    (hb : TM2OutputsInTime b.computer middle (some output) m) :
    TM2OutputsInTime (compose a b).computer input (some output)
      (n + 2 * (middle.length + 1) + m) where
  steps := hb.steps + (2 * (middle.length + 1) + ha.steps)
  evals_in_steps := compose_run a b input middle output ha.steps hb.steps
    ha.evals_in_steps hb.evals_in_steps
  steps_le_m := by have := ha.steps_le_m; have := hb.steps_le_m; omega

/-- Source transitions retain their exact finite primitive syntax budget. -/
theorem compose_left_budget (label : a.Label) :
    TM2Cost.budget (composeProgram a b (firstLabel a b label)) =
      TM2Cost.budget (a.program label) :=
  embed_budget (leftLayout a b) (leftStates a b) (firstLabel a b)
    (some (moveLabel a b)) (a.program label)

theorem compose_right_budget (label : b.Label) :
    TM2Cost.budget (composeProgram a b (secondLabel a b label)) =
      TM2Cost.budget (b.program label) :=
  embed_budget (rightLayout a b) (rightStates a b) (secondLabel a b) none (b.program label)

/-- Each transfer transition performs at most five elementary instructions,
including the optional-bit scratch reset and the loop/return jump. -/
theorem compose_move_budget : TM2Cost.budget (composeProgram a b (moveLabel a b)) = 5 := rfl

theorem compose_restore_budget : TM2Cost.budget (composeProgram a b (restoreLabel a b)) = 5 := rfl

/-- One genuinely fresh temporary stack suffices, even with component aliasing. -/
theorem compose_stack_count : Fintype.card (compose a b).K =
    Fintype.card a.K + Fintype.card b.K + 1 := by
  simp [compose, Keys, Nat.add_assoc]

theorem compose_label_count : Fintype.card (compose a b).Label =
    Fintype.card a.Label + Fintype.card b.Label + 2 := by
  simp [compose, Labels, Nat.add_assoc]

end Machine

/-- The real machine's polynomial time includes transfer and evaluates the second
time polynomial at a proved bound on the intermediate encoded word length. -/
noncomputable def Computes.comp {α β γ : Type} {ea : Encoding α Bool} {eb : Encoding β Bool}
    {ec : Encoding γ Bool} {f : α → β} {g : β → γ}
    (a : Computes ea eb f) (b : Computes eb ec g) (size : PolynomialOutputBound ea eb f) :
    Computes ea ec (g ∘ f) where
  machine := a.machine.compose b.machine
  time := a.time + 2 * (size.bound + 1) + b.time.comp size.bound
  outputs x := by
    have h := Machine.compose_correct a.machine b.machine (ea.encode x) (eb.encode (f x))
      (ec.encode (g (f x))) (a.time.eval (ea.encode x).length)
      (b.time.eval (eb.encode (f x)).length) (a.outputs x) (b.outputs (f x))
    refine { steps := h.steps, evals_in_steps := h.evals_in_steps, steps_le_m := ?_ }
    apply le_trans h.steps_le_m
    have hs := size.length_le x
    have ht := natPolynomial_eval_mono b.time hs
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_one, Polynomial.eval_comp]
    omega

/-- Ordinary `PolyTime`, derived from the actual compiled finite program. -/
noncomputable def compositionPolyTime {α β γ : Type} {ea : Encoding α Bool} {eb : Encoding β Bool}
    {ec : Encoding γ Bool} {f : α → β} {g : β → γ}
    (a : Computes ea eb f) (b : Computes eb ec g) (size : PolynomialOutputBound ea eb f) :
    PolyTime ea ec (g ∘ f) := (a.comp b size).toPolyTime

end Holant.Complexity.BinaryCompose
