import Holant.Proofs.CountingMachines.StandardMachine.CanonicalPaths

set_option backward.isDefEq.respectTransparency false
/-! A literal finite-table TM0 program, independent of counting witnesses, and
its finite-list zipper realization. Undefined rows enter one fresh rejecting
control by a single write. Physical labels are retained verbatim. -/
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.TapeAdapter
open Turing
variable {Γ Q : Type} [Inhabited Γ] [Inhabited Q]

structure Primitive (Γ Q : Type) [Inhabited Γ] [Inhabited Q] where
  table : Bool → TM0.Machine Γ Q
  split : Q → Bool
  main : Q
  verdict : Q → Option Bool
  halted : ∀ q, (verdict q).isSome = true → ∀ bit a, table bit q a = none

namespace Primitive
variable (p : Primitive Γ Q)

def step (token : Option Bool) (c : TM0.Cfg Γ Q) : Option (TM0.Cfg Γ Q) :=
  match token with
  | none => if p.split c.q then none else TM0.step (p.table false) c
  | some bit => if p.split c.q then TM0.step (p.table bit) c else none

def Trace : List (Option Bool) → TM0.Cfg Γ Q → TM0.Cfg Γ Q → Prop
  | [], a, b => a = b
  | token :: rest, a, b => ∃ next, p.step token a = some next ∧ Trace rest next b

def initial (word : List Γ) : TM0.Cfg Γ Q := ⟨p.main, Tape.mk₁ word⟩
def Path (word : List Γ) := {tokens : List (Option Bool) //
  ∃ finish, p.verdict finish.q = some true ∧ p.Trace tokens (p.initial word) finish}

def instruction : TM0.Stmt Γ → Instruction Γ
  | .move .left => .left
  | .move .right => .right
  | .write a => .write a

def model : Model Γ (Option Q) where
  blank := default
  initial := some p.main
  verdict := fun q => match q with | none => some false | some q => p.verdict q
  choose := fun q => match q with | none => false | some q => p.split q
  transition := fun bit q a => match q with
    | none => (none, .write a)
    | some q => match p.table bit q a with
      | none => (none, .write a)
      | some (next, op) => (some next, instruction op)

def tape (c : Config Γ (Option Q)) : Tape Γ :=
  ⟨c.head, ListBlank.mk c.left, ListBlank.mk c.right⟩

def view (c : Config Γ (Option Q)) : Option (TM0.Cfg Γ Q) :=
  c.control.map (fun q => ⟨q, tape c⟩)

@[simp] theorem view_initial (word : List Γ) :
    view (p.model.initialConfig word) = some (p.initial word) := by
  cases word <;> rfl

@[simp] theorem view_some (q : Q) (a : Γ) (L R : List Γ) :
    view (⟨some q, a, L, R⟩ : Config Γ (Option Q)) = some ⟨q, ⟨a,ListBlank.mk L,ListBlank.mk R⟩⟩ := rfl

@[simp] theorem view_none (a : Γ) (L R : List Γ) :
    view (⟨none, a, L, R⟩ : Config Γ (Option Q)) = none := rfl

@[simp] theorem execute_view (bit : Bool) (q : Q) (a : Γ) (L R : List Γ) :
    view (p.model.execute bit ⟨some q,a,L,R⟩) =
      TM0.step (p.table bit) ⟨q,⟨a,ListBlank.mk L,ListBlank.mk R⟩⟩ := by
  cases ht : p.table bit q a with
  | none => simp [Model.execute, model, ht, view, TM0.step]
  | some result =>
      rcases result with ⟨next,op⟩
      cases op with
      | write symbol => simp [Model.execute,model,ht,instruction,view,tape,TM0.step,Tape.write]
      | move d =>
          cases d <;> cases L <;> cases R <;>
            simp [Model.execute,model,ht,instruction,view,tape,TM0.step,Tape.move]

/-- Exact physical correspondence, after erasing only the new rejecting sink.
There is no choice of a tape representative in this equation. -/
theorem physicalStep_view (token : Option Bool) (c : Config Γ (Option Q))
    (a : TM0.Cfg Γ Q) (hc : view c = some a) :
    (p.model.physicalStep token c).bind view = p.step token a := by
  rcases c with ⟨q,head,L,R⟩
  cases q with
  | none => simp [view] at hc
  | some q =>
      have he : (⟨q,⟨head,ListBlank.mk L,ListBlank.mk R⟩⟩ : TM0.Cfg Γ Q) = a := Option.some.inj hc
      subst a
      cases hv : p.verdict q with
      | none =>
          cases token <;> cases hs : p.split q <;>
            simp [Model.physicalStep,Model.step,model,hv,hs,step]
          all_goals exact p.execute_view _ q head L R
      | some verdict =>
          have hstop := p.halted q (by simp [hv])
          cases token <;> cases hs : p.split q <;>
            simp [Model.physicalStep,model,hv,step,hs,TM0.step,hstop]

theorem sink_stops (token : Option Bool) (c : Config Γ (Option Q))
    (hc : view c = none) : p.model.physicalStep token c = none := by
  rcases c with ⟨q,head,L,R⟩
  cases q <;> simp_all [view,Model.physicalStep,model]

theorem accepts_view (c : Config Γ (Option Q)) :
    p.model.Accepts c ↔ ∃ a, view c = some a ∧ p.verdict a.q = some true := by
  rcases c with ⟨q,head,L,R⟩
  cases q <;> simp [Model.Accepts,model,view]

theorem step_lift (token : Option Bool) (c : Config Γ (Option Q))
    (a b : TM0.Cfg Γ Q) (hc : view c = some a) (hs : p.step token a = some b) :
    ∃ d, p.model.physicalStep token c = some d ∧ view d = some b := by
  have h := p.physicalStep_view token c a hc
  rw [hs] at h
  cases ht : p.model.physicalStep token c with
  | none => simp [ht] at h
  | some d => exact ⟨d, rfl, by simpa [ht] using h⟩

theorem trace_lift (tokens : List (Option Bool)) (c : Config Γ (Option Q))
    (a b : TM0.Cfg Γ Q) (hc : view c = some a) (h : p.Trace tokens a b) :
    ∃ d, p.model.PhysicalTrace tokens c d ∧ view d = some b := by
  induction tokens generalizing c a with
  | nil => exact ⟨c,rfl,h ▸ hc⟩
  | cons token rest ih =>
      obtain ⟨next,hs,hr⟩ := h
      obtain ⟨d,hd,hv⟩ := p.step_lift token c a next hc hs
      obtain ⟨e,he,hve⟩ := ih d next hv hr
      exact ⟨e,⟨d,hd,he⟩,hve⟩

end Primitive
end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.TapeAdapter
