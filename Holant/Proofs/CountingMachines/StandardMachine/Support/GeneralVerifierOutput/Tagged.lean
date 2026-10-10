import Holant.Proofs.CountingMachines.StandardMachine.Support.GeneralVerifierOutput.Decoder
import Holant.Proofs.CountingMachines.StandardMachine.Support.BooleanOpcode.NativeExecution

set_option backward.isDefEq.respectTransparency false
/-! Locally checked adaptation of the frozen reference proof. An actual heterogeneous output adapter. The old Boolean
machine executes on its original stack names, injected on the right. Halt is
replaced by one finite observer row which pops the singleton Bool, peeks EOF,
writes Sum.inr b to a fresh four-symbol output stack and resets all control.
No equivalence Bool ≃ Bool ⊕ Bool or alphabet cast is used. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.GeneralVerifierOutput.Tagged
open Turing Computability Holant.Complexity BinaryCompose
open Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support
open Reverse.Staging
variable (a : Machine)

abbrev Stack := Unit ⊕ a.K
abbrev Label := Unit ⊕ a.Label
abbrev State := a.State × Option Bool
def Alphabet : Stack a → Type :=
  HeterogeneousSum.Alphabet (fun _ : Unit => Bool ⊕ Bool) (fun _ : a.K => Bool)
def states : StateEmbedding a.State (State a) where
  put v := (v,none)
  get := Prod.fst
  get_put _ := rfl

def emit : TM2.Stmt (Alphabet a) (Label a) (State a) :=
  .pop (.inr a.output) (fun v head => (v.1,head))
    (.peek (.inr a.output) (fun v head => (v.1,if head.isNone then v.2 else none))
      (.push (.inl ()) (fun v => Sum.inr (v.2.getD false))
        (.load (fun _ => (a.initial,none)) .halt)))

def program : Label a → TM2.Stmt (Alphabet a) (Label a) (State a)
  | .inl _ => emit a
  | .inr label => HeterogeneousSum.rightStmt
      (fun _ : Unit => Bool ⊕ Bool) (fun _ : a.K => Bool)
      (states a) Sum.inr (some (.inl ())) (a.program label)

abbrev computer : FinTM2 where
  K := Stack a
  k₀ := .inr a.input
  k₁ := .inl ()
  Γ := Alphabet a
  Γk₀Fin := Bool.fintype
  Λ := Label a
  main := .inr a.main
  σ := State a
  initialState := (a.initial,none)
  m := program a

abbrev machine : BinaryMachine where
  core := computer a
  alternate := program a
  split _ := false
  alphabets key := by
    cases key with
    | inl _ => exact inferInstanceAs (Fintype (Bool ⊕ Bool))
    | inr _ => exact inferInstanceAs (Fintype Bool)

def cfg (c : a.Config) : (computer a).Cfg :=
  HeterogeneousSum.rightCfg (fun _ : Unit => Bool ⊕ Bool) (fun _ : a.K => Bool)
    (states a) Sum.inr (some (.inl ())) (fun _ => []) c

/-- The source input/output alias, if present, remains an alias of its two
right-hand stack names; only the final tagged result uses the fresh left key. -/
theorem source_alias (h : a.input = a.output) :
    (Sum.inr a.input : Stack a) = Sum.inr a.output := congrArg Sum.inr h

theorem initial_cfg (word : List Bool) :
    cfg a (initList a.computer word) = initList (computer a) word := by
  rw [a.init_eq]
  simp only [cfg,HeterogeneousSum.rightCfg,Option.elim_some,states]
  congr 1
  funext key
  cases key with
  | inl key => cases key; simp [initList,computer,Alphabet,HeterogeneousSum.merge]
  | inr key =>
    by_cases hk : key = a.input
    · subst key
      simp [initList,computer,Alphabet,HeterogeneousSum.merge,wordTape]
    · simp [initList,computer,Alphabet,HeterogeneousSum.merge,wordTape,hk]

theorem source_step (c d : a.Config) (h : a.computer.step c = some d) :
    (computer a).step (cfg a c) = some (cfg a d) := by
  rcases c with ⟨label,v,S⟩
  cases label with
  | none => simp [FinTM2.step,TM2.step] at h
  | some label =>
    have hd : TM2.stepAux (a.program label) v S = d := Option.some.inj h
    subst d
    simp only [cfg,HeterogeneousSum.rightCfg,Option.elim_some,computer,FinTM2.step,
      TM2.step,program]
    exact congrArg some (HeterogeneousSum.right_stepAux
      (fun _ : Unit => Bool ⊕ Bool) (fun _ : a.K => Bool) (states a)
      Sum.inr (some (.inl ())) (a.program label) v (fun _ => []) S)

theorem source_run (n : ℕ) (c d : a.Config)
    (h : (fun z => z.bind a.computer.step)^[n] (some c) = some d) :
    (fun z => z.bind (computer a).step)^[n] (some (cfg a c)) = some (cfg a d) := by
  induction n generalizing c with
  | zero =>
    have he : c = d := Option.some.inj h
    subst d
    rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply] at h ⊢
    cases hs : a.computer.step c with
    | none =>
      have hn : (fun z : Option a.Config => z.bind a.computer.step)^[n] none = none :=
        Function.iterate_fixed (f := fun z : Option a.Config => z.bind a.computer.step) rfl n
      simp only [Option.bind_some,hs,hn] at h
      cases h
    | some next =>
      have ht : (fun z => z.bind a.computer.step)^[n] (some next) = some d := by
        simp only [Option.bind_some,hs] at h
        exact h
      rw [Option.bind_some,source_step a c next hs]
      exact ih next ht

/-- The entire old memory is cleaned by the original whole-run producer.
The observer then physically consumes its singleton and its EOF, and returns
the new machine's complete standard terminal, including initial control. -/
theorem emit_step (b : Bool) :
    (computer a).step (cfg a (haltList a.computer [b])) =
      some (haltList (computer a) [Sum.inr b]) := by
  rw [a.halt_eq]
  simp only [cfg,HeterogeneousSum.rightCfg,Option.elim_none,states,computer,
    FinTM2.step,TM2.step,program,emit,TM2.stepAux,HeterogeneousSum.merge,wordTape,
    Function.update_self,List.head?_cons,List.tail_cons,List.head?_nil,
    Option.isNone_none,if_true,Option.getD_some]
  congr 2
  funext key
  cases key with
  | inl key => cases key; simp [haltList,computer,Alphabet,Function.update,HeterogeneousSum.merge]
  | inr key =>
    by_cases hk : key = a.output
    · subst key
      simp [haltList,computer,Alphabet,Function.update,HeterogeneousSum.merge]
    · simp [haltList,computer,Alphabet,Function.update,HeterogeneousSum.merge,hk]

theorem exact_run (word : List Bool) (b : Bool) (n : ℕ)
    (h : (fun z => z.bind a.computer.step)^[n]
      (some (initList a.computer word)) = some (haltList a.computer [b])) :
    (fun z => z.bind (computer a).step)^[n+1]
      (some (initList (computer a) word)) = some (haltList (computer a) [Sum.inr b]) := by
  have hs := source_run a n _ _ h
  rw [initial_cfg] at hs
  rw [Function.iterate_succ_apply',hs,Option.bind_some,emit_step]

/-- A real reusable adapter for internally produced Boolean Computes. This is
not a free simulation law: its statement table and full run proof are above. -/
def taggedComputes {A : Type} {e : Encoding A Bool} {g : A → Bool}
    (c : Computes e encodingBoolBool g) : PolyTime e (taggedBoolEncoding Bool) g where
  tm := computer c.machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl (Bool ⊕ Bool)
  time := c.time+1
  outputsFun x := by
    change TM2OutputsInTime (computer c.machine) (List.map id (e.encode x))
      (some (List.map id [Sum.inr (g x)])) ((c.time+1).eval (e.encode x).length)
    rw [List.map_id,List.map_id]
    have ho := c.outputs x
    refine { steps := ho.steps+1, evals_in_steps := ?_, steps_le_m := ?_ }
    · exact exact_run c.machine _ _ _ ho.evals_in_steps
    · simpa only [Polynomial.eval_add,Polynomial.eval_one] using Nat.add_le_add_right ho.steps_le_m 1
  finiteAlphabets key := (machine c.machine).alphabets key

@[simp] theorem emit_budget : HeterogeneousCost.budget (emit a) = 5 := rfl
theorem source_budget (label : a.Label) :
    HeterogeneousCost.budget (program a (.inr label)) =
      HeterogeneousCost.budget (a.program label) :=
  HeterogeneousSum.right_budget _ _ _ _ _ _

/-- Ordinary deterministic source transitions and halted padding preserve the
branch log. This makes the resource observer the same actual finite machine. -/
theorem run_eq_hold (n : ℕ) (log : List Bool) (c : (machine a).Config) :
    (machine a).run n (log,c) =
      some (log,(Holant.LocalDrafts.CountingHardness.VerifierRun.holdStep (computer a))^[n] c) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    have ha : (machine a).advance (log,c) =
        some (log,Holant.LocalDrafts.CountingHardness.VerifierRun.holdStep (computer a) c) := by
      cases hl : c.l <;> simp [BinaryMachine.advance,BinaryMachine.step,
        Holant.LocalDrafts.CountingHardness.VerifierRun.holdStep,hl,machine]
    rw [BinaryMachine.run,ha,Option.bind_some,ih,Function.iterate_succ_apply]

theorem run_at_bound {A : Type} {e : Encoding A Bool} {g : A → Bool}
    (c : Computes e encodingBoolBool g) (x : A) (log : List Bool) :
    (machine c.machine).run ((c.time+1).eval (e.encode x).length)
      (log,initList (computer c.machine) (e.encode x)) =
        some (log,haltList (computer c.machine) [Sum.inr (g x)]) := by
  rw [run_eq_hold]
  have ho := (taggedComputes c).outputsFun x
  change TM2OutputsInTime (computer c.machine) (List.map id (e.encode x))
    (some (List.map id [Sum.inr (g x)])) ((c.time+1).eval (e.encode x).length) at ho
  rw [List.map_id,List.map_id] at ho
  rw [Holant.LocalDrafts.CountingHardness.VerifierRun.outputs_at_bound (computer c.machine) _ _ _ ho]

/-- No static decode branch or output observer introduces a nondeterministic
edge. This covers the old verifier rows and canonical halted padding as well. -/
theorem trace_tokens_none (bits : List (Option Bool)) (c d : (machine a).Config)
    (h : (machine a).TraceValid bits c d) :
    bits = List.replicate bits.length none := by
  induction bits generalizing c with
  | nil => rfl
  | cons token bits ih =>
    obtain ⟨next,hs,ht⟩ := h
    cases token with
    | some bit =>
      cases hl : c.l <;> simp [BinaryMachine.step,machine,hl] at hs
    | none =>
      simpa only [List.length_cons,List.replicate_succ] using
        congrArg (none::·) (ih next ht)
end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.GeneralVerifierOutput.Tagged
