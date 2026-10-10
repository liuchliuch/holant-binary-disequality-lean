import Mathlib.Computability.StateTransition

set_option backward.isDefEq.respectTransparency false
/-!
# Timed simulation of actual execution prefixes

These helpers compose already proved macro executions of an existing target step
function. They do not introduce machine instructions or permit arbitrary functions
on unbounded configurations inside finite programs. In applications, `f` and `g`
are the actual transition functions of the source and target machines.

The simulation hypothesis can use the exact reachable source prefix and its index.
Consequently, query validity, query size, and other actual-run invariants can be
used to justify each macro. The returned witness is data in `Type`, so its actual
endpoint and timed execution can be used directly in machine correctness proofs.
-/

namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.TimedSimulation

variable {A B : Type*}

/-- A target execution ending at a state related to the given source endpoint. -/
structure Witness (g : B → Option B) (R : A → B → Prop)
    (start : B) (source : A) (time : ℕ) where
  target : B
  related : R source target
  evaluation : StateTransition.EvalsToInTime g start (some target) time

/-- Increase an upper bound without changing the actual execution or endpoint. -/
def Witness.mono {g : B → Option B} {R : A → B → Prop}
    {start : B} {source : A} {m n : ℕ} (w : Witness g R start source m)
    (h : m ≤ n) : Witness g R start source n where
  target := w.target
  related := w.related
  evaluation :=
    { w.evaluation with steps_le_m := le_trans w.evaluation.steps_le_m h }

/-- Simulate exactly `n` successful source transitions. Only source states on the
given actual run, and only indices strictly before `n`, need a macro contract. -/
def liftPrefix (f : A → Option A) (g : B → Option B) (R : A → B → Prop)
    (a₀ : A) (b₀ : B) (initial : R a₀ b₀) (n C : ℕ)
    (simulate : ∀ t, t < n → ∀ a a' b,
      (fun p => p.bind f)^[t] (some a₀) = some a →
      f a = some a' → R a b → Witness g R b a' C)
    (a : A) (run : (fun p => p.bind f)^[n] (some a₀) = some a) :
    Witness g R b₀ a (n * C) := by
  induction n generalizing a with
  | zero =>
    have ha : a₀ = a := Option.some.inj run
    subst a
    refine ⟨b₀, initial, ?_⟩
    simpa only [Nat.zero_mul] using StateTransition.EvalsToInTime.refl g b₀
  | succ n ih =>
    rw [Function.iterate_succ_apply'] at run
    cases hp : (fun p => p.bind f)^[n] (some a₀) with
    | none => simp [hp] at run
    | some previous =>
      have hs : f previous = some a := by simpa [hp] using run
      let earlier := ih (fun t ht => simulate t (Nat.lt_trans ht (Nat.lt_succ_self n)))
        previous hp
      let next := simulate n (Nat.lt_succ_self n) previous a earlier.target hp hs earlier.related
      refine ⟨next.target, next.related, ?_⟩
      have joined := StateTransition.EvalsToInTime.trans g (n * C) C b₀ earlier.target
        (some next.target) earlier.evaluation next.evaluation
      simpa only [Nat.succ_mul, Nat.add_comm] using joined

/-- Lift a successful timed source run. The source's recorded transition count
may be strictly smaller than its bound, and no macros beyond that count run. -/
def liftTimed (f : A → Option A) (g : B → Option B) (R : A → B → Prop)
    (a₀ : A) (b₀ : B) (initial : R a₀ b₀) (time C : ℕ)
    (simulate : ∀ t, t < time → ∀ a a' b,
      (fun p => p.bind f)^[t] (some a₀) = some a →
      f a = some a' → R a b → Witness g R b a' C)
    (a : A) (run : StateTransition.EvalsToInTime f a₀ (some a) time) :
    Witness g R b₀ a (time * C) :=
  (liftPrefix f g R a₀ b₀ initial run.steps C
    (fun t ht => simulate t (Nat.lt_of_lt_of_le ht run.steps_le_m))
    a run.evals_in_steps).mono (Nat.mul_le_mul_right C run.steps_le_m)

/-- A condition initialized at the source start and preserved by transitions
holds at every successful actual prefix within the supplied horizon. -/
theorem invariant_of_prefix (f : A → Option A) (P : ℕ → A → Prop)
    (a₀ : A) (initial : P 0 a₀) (n : ℕ)
    (preserved : ∀ t, t < n → ∀ a a', P t a → f a = some a' → P (t + 1) a')
    (t : ℕ) (ht : t ≤ n) (a : A)
    (run : (fun p => p.bind f)^[t] (some a₀) = some a) : P t a := by
  induction t generalizing a with
  | zero =>
    have ha : a₀ = a := Option.some.inj run
    simpa only [← ha] using initial
  | succ t ih =>
    rw [Function.iterate_succ_apply'] at run
    cases hp : (fun p => p.bind f)^[t] (some a₀) with
    | none => simp [hp] at run
    | some previous =>
      have hs : f previous = some a := by simpa [hp] using run
      exact preserved t (Nat.lt_of_lt_of_le (Nat.lt_succ_self t) ht) previous a
        (ih (Nat.le_trans (Nat.le_succ t) ht) previous hp) hs

/-- Convenient invariant-based form: derive the needed source condition from its
initial value and preservation, then compose the actual target macro executions. -/
def liftTimedOfInvariant (f : A → Option A) (g : B → Option B)
    (R : A → B → Prop) (P : ℕ → A → Prop) (a₀ : A) (b₀ : B)
    (initial : R a₀ b₀) (initialP : P 0 a₀) (time C : ℕ)
    (preserved : ∀ t, t < time → ∀ a a', P t a → f a = some a' → P (t + 1) a')
    (simulate : ∀ t, t < time → ∀ a a' b,
      P t a → f a = some a' → R a b → Witness g R b a' C)
    (a : A) (run : StateTransition.EvalsToInTime f a₀ (some a) time) :
    Witness g R b₀ a (time * C) :=
  liftTimed f g R a₀ b₀ initial time C
    (fun t ht a a' b hprefix step related => simulate t ht a a' b
      (invariant_of_prefix f P a₀ initialP time preserved t (Nat.le_of_lt ht) a hprefix)
      step related) a run

end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.TimedSimulation
