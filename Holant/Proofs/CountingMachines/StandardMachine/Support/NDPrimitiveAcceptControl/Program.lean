import Holant.Proofs.CountingMachines.StandardMachine.Support.NDPrimitiveFrontend.Program

set_option backward.isDefEq.respectTransparency false
/-! Adapted reference proof. See the task validation reports. A finite accepting-control successor of the installed
raw-input primitive machine. It observes a whole finite head column and the
finite variable store, physically moves right once, and reads strict EOF.
No tape decoder, desired verdict or acceptance law is a programme parameter. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.NDPrimitiveAcceptControl.Program
open Turing Computability Holant.Complexity
namespace Old
export NDPrimitiveFrontend.Program (machine Symbol Control Cfg table choose step initial lift inclusion)
end Old
namespace Native
export NDPrimitiveDispatcher.Program (Alphabet Cfg Control embed Halted haltCfg forgetNode)
end Native
variable {α Γ : Type} [Fintype Γ] {ea : Encoding α Γ} {f : α → ℕ} (w : SharpPWitness ea f)
abbrev machine := Old.machine w
abbrev Symbol := Old.Symbol w
inductive Phase | probe | accept | reject deriving Fintype, DecidableEq
abbrev Control := Old.Control w ⊕ Phase
instance : Fintype (Control w) := inferInstance
instance : Inhabited (Control w) := ⟨.inl default⟩
abbrev Cfg := TM0.Cfg (Symbol w) (Control w)
local instance : DecidableEq (Symbol w) := Classical.decEq _
local instance : DecidableEq (machine w).core.σ := Classical.decEq _

def terminal : Old.Control w → Bool
  | .inl _ => false
  | .inr (.inl _,_) => false
  | .inr (.inr pc,_) => pc.val.isNone
theorem terminal_right (q : Old.Control w) (h : terminal w q = true) : q.isLeft = false := by
  cases q with
  | inl s => simp [terminal] at h
  | inr q => rfl
theorem terminal_native (c : Native.Cfg (machine w)) :
    terminal w (Old.lift w c).q = true ↔ Native.Halted (machine w) c := by
  rcases c with ⟨⟨node,v⟩,T⟩
  cases node with
  | inl l => simp [terminal,Old.lift,Native.Halted,Native.forgetNode]
  | inr pc => cases hv : pc.val <;> simp [terminal,Old.lift,Native.Halted,Native.forgetNode,hv]
theorem terminal_choose (q : Old.Control w) (h : terminal w q = true) : Old.choose w q = false := by
  cases q with
  | inl s => simp [terminal] at h
  | inr q =>
      rcases q with ⟨node,v⟩
      cases node with
      | inl l => simp [terminal] at h
      | inr pc => rfl

def trueColumn : Native.Alphabet (machine w) :=
  (true,Function.update (fun _ => none) (machine w).core.k₁ (some true))
def headGood : Old.Control w → Symbol w → Bool
  | .inl _,_ => false
  | .inr (_,v),a => decide (v = (machine w).core.initialState) && decide (a = .native (trueColumn w))

def table (bit : Bool) : TM0.Machine (Symbol w) (Control w)
  | .inl q,a => if terminal w q then
      if headGood w q a then some (.inr .probe,.move .right)
      else some (.inr .reject,.write a)
    else (Old.table w bit q a).map (fun r => (.inl r.1,r.2))
  | .inr .probe,a => some (.inr (if a = default then .accept else .reject),.write a)
  | .inr .accept,_ => none
  | .inr .reject,_ => none
def choose : Control w → Bool | .inl q => Old.choose w q | .inr _ => false
def step (token : Option Bool) (c : Cfg w) : Option (Cfg w) :=
  match token with
  | none => if choose w c.q then none else TM0.step (table w false) c
  | some b => if choose w c.q then TM0.step (table w b) c else none
structure ProgrammeData (A S : Type) [Inhabited S] where
  core : TM0.Machine A S
  alternate : TM0.Machine A S
  split : S → Bool
  main : S
  accept : S
  reject : S
abbrev Programme := ProgrammeData (Symbol w) (Control w)
def programme : Programme w := ⟨table w false,table w true,choose w,default,.inr .accept,.inr .reject⟩
def lift (c : Old.Cfg w) : Cfg w := ⟨.inl c.q,c.Tape⟩
def initial (word : List Bool) : Cfg w := TM0.init (NDPrimitiveFrontend.Program.rawWord w word)
theorem initial_lift (word : List Bool) : initial w word = lift w (Old.initial w word) := rfl
theorem lift_injective : Function.Injective (lift w) := by
  intro a b h
  have hq := Sum.inl.inj (congrArg TM0.Cfg.q h)
  have ht := congrArg TM0.Cfg.Tape h
  cases a; cases b; cases hq; cases ht; rfl
theorem active_step (token : Option Bool) (c : Old.Cfg w) (hc : terminal w c.q = false) :
    step w token (lift w c) = (Old.step w token c).map (lift w) := by
  rcases c with ⟨q,T⟩
  cases token with
  | none =>
      cases hs : Old.choose w q
      · cases ht : Old.table w false q T.head with
        | none => simp [step,choose,lift,table,Old.step,TM0.step,hs,ht,hc]
        | some r => rcases r with ⟨next,op⟩; cases op <;> simp [step,choose,lift,table,Old.step,TM0.step,hs,ht,hc]
      · simp [step,choose,lift,Old.step,hs]
  | some bit =>
      cases hs : Old.choose w q
      · simp [step,choose,lift,Old.step,hs]
      · cases ht : Old.table w bit q T.head with
        | none => simp [step,choose,lift,table,Old.step,TM0.step,hs,ht,hc]
        | some r => rcases r with ⟨next,op⟩; cases op <;> simp [step,choose,lift,table,Old.step,TM0.step,hs,ht,hc]

theorem terminal_old_stops (c : Old.Cfg w) (hc : terminal w c.q = true) (token : Option Bool) :
    Old.step w token c = none := by
  rcases c with ⟨q,T⟩
  cases q with
  | inl s => simp [terminal] at hc
  | inr q =>
      rcases q with ⟨node,v⟩
      cases node with
      | inl l => simp [terminal] at hc
      | inr pc =>
          rcases pc with ⟨raw,hraw⟩
          have hp : raw = none := Option.isNone_iff_eq_none.mp hc
          subst raw
          cases hh : T.head <;> cases token <;>
            simp [Old.step,Old.choose,Old.table,NDPrimitiveDispatcher.Program.step,
              NDPrimitiveDispatcher.Program.choose,NDPrimitiveDispatcher.Program.table,TM0.step,hh]
theorem phase_no_choice (phase : Phase) (T : Tape (Symbol w)) (bit : Bool) :
    step w (some bit) ⟨.inr phase,T⟩ = none := rfl
theorem accept_stops (T : Tape (Symbol w)) (token : Option Bool) :
    step w token ⟨.inr .accept,T⟩ = none := by cases token <;> rfl
theorem reject_stops (T : Tape (Symbol w)) (token : Option Bool) :
    step w token ⟨.inr .reject,T⟩ = none := by cases token <;> rfl
theorem entry_step (c : Old.Cfg w) (hc : terminal w c.q = true) :
    step w none (lift w c) = some (if headGood w c.q c.Tape.head then
      ⟨.inr .probe,c.Tape.move .right⟩ else ⟨.inr .reject,c.Tape⟩) := by
  cases hg : headGood w c.q c.Tape.head <;>
    simp [step,choose,lift,table,TM0.step,hc,terminal_choose w c.q hc,hg,Tape.write_self]
theorem entry_no_choice (c : Old.Cfg w) (hc : terminal w c.q = true) (bit : Bool) :
    step w (some bit) (lift w c) = none := by simp [step,choose,lift,terminal_choose w c.q hc]
theorem probe_step (T : Tape (Symbol w)) :
    step w none ⟨.inr .probe,T⟩ = some ⟨.inr (if T.head = default then .accept else .reject),T⟩ := by
  simp [step,choose,table,TM0.step,Tape.write_self]

end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.NDPrimitiveAcceptControl.Program
