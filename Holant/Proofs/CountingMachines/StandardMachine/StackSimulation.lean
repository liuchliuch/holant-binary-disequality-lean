import Holant.Proofs.CountingMachines.StandardMachine.Model
import Holant.Proofs.CountingMachines.StandardMachine.Support.Foundation

set_option backward.isDefEq.respectTransparency false
/-! Literal two-stack implementation of the independent move/write machine.
One deterministic row loads the input head. Thereafter every original physical
instruction has one compiled TM2 transition with exactly the same edge label.
Every primitive in each fixed statement reads or changes at most one symbol.
-/
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine
open Turing Computability Holant.Complexity

namespace Model
variable {Γ Q : Type} [Fintype Γ] [Fintype Q] (m : Model Γ Q)

private def isLeft : Instruction Γ → Bool
  | .left => true
  | _ => false
private def isRight : Instruction Γ → Bool
  | .right => true
  | _ => false
private def writeValue : Instruction Γ → Γ
  | .write a => a
  | _ => m.blank

abbrev StackState := Q × Γ
abbrev StackLabel := Unit ⊕ Q
abbrev Statement := TM2.Stmt (fun _ : Bool => Γ) (StackLabel (Q := Q)) (StackState (Γ := Γ) (Q := Q))

def stackWords (left right : List Γ) : Bool → List Γ := fun b => if b then right else left

@[simp] theorem stackWords_false (left right : List Γ) : stackWords left right false = left := rfl
@[simp] theorem stackWords_true (left right : List Γ) : stackWords left right true = right := rfl

private theorem stackWords_update_false (left right word : List Γ) :
    Function.update (stackWords left right) false word = stackWords word right := by
  funext k; cases k <;> simp [stackWords]
private theorem stackWords_update_true (left right word : List Γ) :
    Function.update (stackWords left right) true word = stackWords left word := by
  funext k; cases k <;> simp [stackWords]

/-- The verdict is inspected only in finite control. -/
def finish : Statement (Γ := Γ) (Q := Q) :=
  .branch (fun v => (m.verdict v.1).isSome) .halt (.goto (fun v => .inr v.1))

/-- The transition table is a finite lookup on the old control and head symbol.
All list manipulation below is an actual push or pop instruction. -/
def instruction (bit : Bool) (q : Q) : Statement (Γ := Γ) (Q := Q) :=
  .load (fun v => ((m.transition bit q v.2).1, v.2))
    (.branch (fun v => isLeft (m.transition bit q v.2).2)
      (.push true Prod.snd (.pop false (fun v a => (v.1, a.getD m.blank)) (m.finish)))
      (.branch (fun v => isRight (m.transition bit q v.2).2)
        (.push false Prod.snd (.pop true (fun v a => (v.1, a.getD m.blank)) (m.finish)))
        (.load (fun v => (v.1, m.writeValue (m.transition bit q v.2).2)) (m.finish))))

def program (bit : Bool) : StackLabel (Q := Q) → Statement (Γ := Γ) (Q := Q)
  | .inl _ => .pop true (fun v a => (v.1, a.getD m.blank)) m.finish
  | .inr q => m.instruction bit q

noncomputable def computer : FinTM2 where
  K := Bool
  k₀ := true
  k₁ := false
  Γ _ := Γ
  Λ := StackLabel (Q := Q)
  main := .inl ()
  σ := StackState (Γ := Γ) (Q := Q)
  initialState := (m.initial, m.blank)
  m := m.program false

noncomputable def toBinary : Support.BinaryMachine where
  core := m.computer
  alternate := m.program true
  split
    | .inl _ => false
    | .inr q => m.choose q
  alphabets _ := inferInstanceAs (Fintype Γ)

noncomputable def embed (c : Config Γ Q) : m.toBinary.Config :=
  ⟨if (m.verdict c.control).isSome then none else some (.inr c.control),
    (c.control, c.head), stackWords c.left c.right⟩

theorem embed_injective : Function.Injective m.embed := by
  intro a b h
  have hs := congrArg (fun c : m.toBinary.Config => c.var) h
  have hl := congrArg (fun c : m.toBinary.Config => c.stk false) h
  have hr := congrArg (fun c : m.toBinary.Config => c.stk true) h
  cases a; cases b
  simp only [embed, Prod.mk.injEq, stackWords_false, stackWords_true] at hs hl hr
  obtain ⟨hq, hh⟩ := Prod.mk.inj hs
  cases hq; cases hh; cases hl; cases hr; rfl

private theorem finish_exec (q : Q) (head : Γ) (left right : List Γ) :
    TM2.stepAux m.finish (q, head) (stackWords left right) =
      m.embed ⟨q, head, left, right⟩ := by
  cases hv : (m.verdict q).isSome <;>
    simp [finish, TM2.stepAux, embed, hv] <;> rfl

/-- The installed finite statement realizes a single source move or write. -/
theorem instruction_exec (bit : Bool) (c : Config Γ Q) :
    TM2.stepAux (m.instruction bit c.control) (c.control, c.head)
      (stackWords c.left c.right) = m.embed (m.execute bit c) := by
  cases ht : m.transition bit c.control c.head with
  | mk next op =>
      cases op <;>
        simp only [instruction, TM2.stepAux, ht, isLeft, isRight, writeValue,
          Bool.false_eq_true, ite_false, ite_true, stackWords_false, stackWords_true,
          stackWords_update_false, stackWords_update_true, finish_exec, execute]
      all_goals rfl

/-- Step-for-step simulation, including illegal labels and unique halt padding. -/
theorem step_embed (token : Option Bool) (c : Config Γ Q) :
    m.toBinary.step token (m.embed c) = (m.step token c).map m.embed := by
  cases hv : m.verdict c.control with
  | some b => cases token <;> simp [Support.BinaryMachine.step, embed, step, hv]
  | none =>
      cases token with
      | none =>
          cases hc : m.choose c.control <;>
            simp [Support.BinaryMachine.step, embed, step, hv, toBinary, computer, program, hc,
              instruction_exec]
      | some bit =>
          cases hc : m.choose c.control <;> cases bit <;>
            simp [Support.BinaryMachine.step, embed, step, hv, toBinary, computer, program, hc,
              instruction_exec]

/-- The initialization overhead is a real deterministic pop, independent of
input length. Original input symbols are loaded without changing their alphabet. -/
theorem initialize_step (word : List Γ) :
    m.toBinary.step none (initList m.computer word) =
      some (m.embed (m.initialConfig word)) := by
  have hw : (initList m.computer word).stk = stackWords [] word := by
    funext k
    cases k <;> simp [initList, computer, stackWords]
  simp only [Support.BinaryMachine.step, initList, computer, toBinary, program]
  change some (TM2.stepAux
    (.pop true (fun v a => (v.1, a.getD m.blank)) m.finish)
    (m.initial, m.blank) (initList m.computer word).stk) = _
  rw [hw]
  simp only [TM2.stepAux, stackWords_true, stackWords_update_true, finish_exec, initialConfig]

/-- The special input-loader label cannot consume a branch bit. -/
theorem initialize_no_choice (word : List Γ) (b : Bool) :
    m.toBinary.step (some b) (initList m.computer word) = none := by
  simp [Support.BinaryMachine.step, initList, computer, toBinary]

theorem trace_embed (tokens : List (Option Bool)) (c d : Config Γ Q) :
    m.toBinary.TraceValid tokens (m.embed c) (m.embed d) ↔ m.Trace tokens c d := by
  induction tokens generalizing c with
  | nil =>
      change (m.embed c = m.embed d) ↔ c = d
      exact ⟨fun h => m.embed_injective h, congrArg m.embed⟩
  | cons token rest ih =>
      constructor
      · rintro ⟨next, hs, ht⟩
        rw [step_embed] at hs
        cases he : m.step token c with
        | none => simp [he] at hs
        | some middle =>
            have hn : m.embed middle = next := Option.some.inj (by simpa [he] using hs)
            subst next
            exact ⟨middle, he, (ih middle).mp ht⟩
      · rintro ⟨middle, hs, ht⟩
        exact ⟨m.embed middle, by rw [step_embed, hs]; rfl, (ih middle).mpr ht⟩

/-- Completeness excludes invented target endpoints or phantom branches. -/
theorem trace_lift (tokens : List (Option Bool)) (c : Config Γ Q)
    (d : m.toBinary.Config) (h : m.toBinary.TraceValid tokens (m.embed c) d) :
    ∃ finish, d = m.embed finish ∧ m.Trace tokens c finish := by
  induction tokens generalizing c with
  | nil => exact ⟨c, h.symm, rfl⟩
  | cons token rest ih =>
      obtain ⟨next, hs, ht⟩ := h
      rw [step_embed] at hs
      cases he : m.step token c with
      | none => simp [he] at hs
      | some middle =>
          have hn : m.embed middle = next := Option.some.inj (by simpa [he] using hs)
          subst next
          obtain ⟨finish, hd, hr⟩ := ih middle ht
          exact ⟨finish, hd, middle, he, hr⟩

def acceptControl : StackState (Γ := Γ) (Q := Q) → Bool :=
  fun v => (m.verdict v.1).getD false

theorem accepts_embed (c : Config Γ Q) :
    (m.embed c).l = none ∧ m.acceptControl (m.embed c).var = true ↔ m.Accepts c := by
  cases hv : m.verdict c.control with
  | none => simp [embed, acceptControl, Accepts, hv]
  | some b => cases b <;> simp [embed, acceptControl, Accepts, hv]

end Model
end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine
