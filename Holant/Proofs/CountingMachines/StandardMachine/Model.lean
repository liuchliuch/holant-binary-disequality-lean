import Holant.Proofs.CountingMachines.Interface

set_option backward.isDefEq.respectTransparency false
/-!
# An independent finite, binary nondeterministic one-tape machine

A tape is represented by its head symbol and two finite lists, nearest cell
first. Beyond either list every cell is the distinguished blank. Keeping
explicit blank cells is harmless: they are never chosen by an execution and
each labelled history determines exactly one representation. An instruction
performs one physical move or one write. All tests and transition tables have
finite domains; there is no operation on an entire tape or configuration.

`none` labels a deterministic edge. `some false` and `some true` label the two
edges at a choice control, even if their successor configurations coincide.
A stopped control has precisely the canonical `none` padding edge. Padding is
separate from the physical stopping/time condition.
-/
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine
open Turing Computability Holant.Complexity

inductive Instruction (Γ : Type)
  | left
  | right
  | write (symbol : Γ)
  deriving DecidableEq

structure Config (Γ Q : Type) where
  control : Q
  head : Γ
  left : List Γ
  right : List Γ
  deriving DecidableEq

/-- Finite control, finite alphabet and literal move/write transition tables.
The ambient `Fintype` instances are required by compilation, independently of
this executable transition semantics. `verdict = none` means running. -/
structure Model (Γ Q : Type) where
  blank : Γ
  initial : Q
  verdict : Q → Option Bool
  choose : Q → Bool
  transition : Bool → Q → Γ → Q × Instruction Γ

namespace Model
variable {Γ Q : Type} (m : Model Γ Q)

def initialConfig (word : List Γ) : Config Γ Q :=
  ⟨m.initial, word.head?.getD m.blank, [], word.tail⟩

/-- Execute exactly one selected instruction. -/
def execute (b : Bool) (c : Config Γ Q) : Config Γ Q :=
  let next := m.transition b c.control c.head
  match next.2 with
  | .left => ⟨next.1, c.left.head?.getD m.blank, c.left.tail, c.head :: c.right⟩
  | .right => ⟨next.1, c.right.head?.getD m.blank, c.head :: c.left, c.right.tail⟩
  | .write symbol => ⟨next.1, symbol, c.left, c.right⟩

def step (token : Option Bool) (c : Config Γ Q) : Option (Config Γ Q) :=
  match m.verdict c.control, token with
  | some _, none => some c
  | some _, some _ => none
  | none, none => if m.choose c.control then none else some (m.execute false c)
  | none, some b => if m.choose c.control then some (m.execute b c) else none

/-- Physical transitions have no successor after accept or reject. -/
def physicalStep (token : Option Bool) (c : Config Γ Q) : Option (Config Γ Q) :=
  if (m.verdict c.control).isSome then none else m.step token c

def Trace : List (Option Bool) → Config Γ Q → Config Γ Q → Prop
  | [], c, d => c = d
  | token :: rest, c, d => ∃ next, m.step token c = some next ∧ Trace rest next d

def PhysicalTrace : List (Option Bool) → Config Γ Q → Config Γ Q → Prop
  | [], c, d => c = d
  | token :: rest, c, d =>
      ∃ next, m.physicalStep token c = some next ∧ PhysicalTrace rest next d

def Accepts (c : Config Γ Q) : Prop := m.verdict c.control = some true

def AcceptedPath (horizon : ℕ) (word : List Γ) :=
  {tokens : List (Option Bool) // tokens.length = horizon ∧
    ∃ finish, m.Accepts finish ∧ m.Trace tokens (m.initialConfig word) finish}

/-- Source membership data: every real execution prefix fits this polynomial.
No simulation or verifier complexity is presumed. -/
def PolyTime (clock : Polynomial ℕ) : Prop :=
  ∀ (word : List Γ) (tokens : List (Option Bool)) (finish : Config Γ Q),
    m.PhysicalTrace tokens (m.initialConfig word) finish →
      tokens.length ≤ clock.eval word.length

@[simp] theorem step_halted (c : Config Γ Q) (b : Bool)
    (h : m.verdict c.control = some b) : m.step none c = some c := by
  simp [step, h]

@[simp] theorem step_halted_choice (c : Config Γ Q) (b bit : Bool)
    (h : m.verdict c.control = some b) : m.step (some bit) c = none := by
  simp [step, h]

theorem physicalStep_halted (c : Config Γ Q) (b : Bool)
    (h : m.verdict c.control = some b) (token : Option Bool) :
    m.physicalStep token c = none := by simp [physicalStep, h]

theorem trace_unique (tokens : List (Option Bool)) (start a b : Config Γ Q)
    (ha : m.Trace tokens start a) (hb : m.Trace tokens start b) : a = b := by
  induction tokens generalizing start with
  | nil => exact ha.symm.trans hb
  | cons token rest ih =>
      obtain ⟨ca, hca, hta⟩ := ha
      obtain ⟨cb, hcb, htb⟩ := hb
      have he : ca = cb := Option.some.inj (hca.symm.trans hcb)
      subst cb
      exact ih ca hta htb

theorem trace_append (xs ys : List (Option Bool)) (a b c : Config Γ Q)
    (hxs : m.Trace xs a b) (hys : m.Trace ys b c) : m.Trace (xs ++ ys) a c := by
  induction xs generalizing a with
  | nil => subst b; exact hys
  | cons token rest ih =>
      obtain ⟨next, hs, ht⟩ := hxs
      exact ⟨next, hs, ih next ht⟩

theorem trace_halted (tokens : List (Option Bool)) (c d : Config Γ Q) (b : Bool)
    (hc : m.verdict c.control = some b) :
    m.Trace tokens c d ↔ tokens = List.replicate tokens.length none ∧ c = d := by
  induction tokens generalizing d with
  | nil => simp [Trace]
  | cons token rest ih =>
      cases token with
      | none =>
          constructor
          · rintro ⟨next, hs, ht⟩
            have he : c = next := Option.some.inj ((m.step_halted c b hc).symm.trans hs)
            subst next
            obtain ⟨hw, hd⟩ := (ih d).mp ht
            exact ⟨by simpa only [List.length_cons, List.replicate_succ] using congrArg (none :: ·) hw, hd⟩
          · rintro ⟨hw, hd⟩
            have hr : rest = List.replicate rest.length none := by
              simpa only [List.length_cons, List.replicate_succ, List.cons.injEq, true_and] using hw
            exact ⟨c, m.step_halted c b hc, (ih d).mpr ⟨hr, hd⟩⟩
      | some bit =>
          simp [Trace, step_halted_choice m c b bit hc, List.replicate_succ]

/-- A stopped machine admits exactly one padding word of a prescribed length. -/
theorem canonical_padding (n : ℕ) (c : Config Γ Q) (b : Bool)
    (hc : m.verdict c.control = some b) :
    m.Trace (List.replicate n none) c c := by
  exact (m.trace_halted _ c c b hc).mpr ⟨by simp, rfl⟩

/-- Branch identity is the label word, even when the selected tables agree. -/
theorem distinct_choice_words (rest : List (Option Bool)) :
    (some false :: rest) ≠ (some true :: rest) := by simp

def cells (_m : Model Γ Q) (c : Config Γ Q) : ℕ := c.left.length + c.right.length + 1

theorem execute_cells (bit : Bool) (c : Config Γ Q) :
    m.cells (m.execute bit c) ≤ m.cells c + 1 := by
  cases ht : (m.transition bit c.control c.head).2 <;>
    simp [execute, ht, cells, List.length_tail] <;> omega

theorem step_cells (token : Option Bool) (c d : Config Γ Q)
    (h : m.step token c = some d) : m.cells d ≤ m.cells c + 1 := by
  cases hv : m.verdict c.control with
  | some b =>
      cases token with
      | none =>
          have he : c = d := Option.some.inj (by simpa [step, hv] using h)
          subst d; omega
      | some bit => simp [step, hv] at h
  | none =>
      cases token with
      | none =>
          cases hc : m.choose c.control
          · have he : m.execute false c = d := Option.some.inj (by simpa [step, hv, hc] using h)
            subst d; exact m.execute_cells false c
          · simp [step, hv, hc] at h
      | some bit =>
          cases hc : m.choose c.control
          · simp [step, hv, hc] at h
          · have he : m.execute bit c = d := Option.some.inj (by simpa [step, hv, hc] using h)
            subst d; exact m.execute_cells bit c

theorem trace_cells (tokens : List (Option Bool)) (c d : Config Γ Q)
    (h : m.Trace tokens c d) : m.cells d ≤ m.cells c + tokens.length := by
  induction tokens generalizing c with
  | nil => subst d; simp
  | cons token rest ih =>
      obtain ⟨next, hs, ht⟩ := h
      have hstep := m.step_cells token c next hs
      have hrest := ih next ht
      simp only [List.length_cons]
      omega

theorem initial_cells (word : List Γ) : m.cells (m.initialConfig word) ≤ word.length + 1 := by
  simp [cells, initialConfig, List.length_tail]

theorem prefix_cells (word : List Γ) (tokens : List (Option Bool)) (d : Config Γ Q)
    (h : m.Trace tokens (m.initialConfig word) d) :
    m.cells d ≤ word.length + tokens.length + 1 := by
  have hs := m.trace_cells tokens _ d h
  have hi := m.initial_cells word
  omega

end Model
end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine
