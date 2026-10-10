import Holant.Proofs.CountingMachines.StandardMachine.Support.NDPrimitiveDispatcher.Program
import Holant.Proofs.CountingMachines.StandardMachine.Support.TotalRawSource

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
/-! Adapted reference proof. See the task validation reports. Raw Bool letters are distinct from tape blank, so a
trailing false bit is physically present. No reversed/coded tape, length,
decoder result or source-ready configuration is supplied as machine input.
The finite frontend scans/writes EOF and fence, copies one real bit at a time
to the left, and installs the SAME old primitive dispatcher after cleanup. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.NDPrimitiveFrontend.Program
open Turing Computability Holant.Complexity
namespace Native
export NDPrimitiveDispatcher.Program (Alphabet Control table choose step)
end Native
variable {α Γ : Type} [Fintype Γ] {ea : Encoding α Γ} {f : α → ℕ} (w : SharpPWitness ea f)
abbrev machine := TotalRawSource.source w
local instance : Fintype (Native.Alphabet (machine w)) := TapeSimulation.alphabetFinite (machine w)
/-- Generic finite sum avoids expanding a compiled machine during positivity
checking. Its four literal constructors are exactly the physical alphabet. -/
inductive Symbols (A : Type)
  | native : A → Symbols A
  | raw : Bool → Symbols A
  | fence : Symbols A
  | eof : Symbols A
deriving Fintype
abbrev Symbol := Symbols (Native.Alphabet (machine w))
namespace Symbol
export Symbols (native raw fence eof)
end Symbol

namespace Symbol.raw
export Symbols.raw (inj)
end Symbol.raw
instance : Inhabited (Symbol w) := ⟨.native default⟩
local instance : DecidableEq (Symbol w) := Classical.decEq _
local instance : DecidableEq (Native.Alphabet (machine w)) := Classical.decEq _

inductive Front
  | start | putFence | toInput | scanEnd | returnLeft | skipInput
  | copyLeft : Bool → Front
  | outLeft : Bool → Front
  | backFence | finishLeft | leftStart | seekBottom | markBottom | reject
deriving Fintype, DecidableEq
abbrev Control := Front ⊕ Native.Control (machine w)
instance : Fintype (Control w) := inferInstance
instance : Inhabited (Control w) := ⟨.inl .start⟩
abbrev Cfg := TM0.Cfg (Symbol w) (Control w)

def column (b : Bool) : Native.Alphabet (machine w) :=
  (false,Function.update (fun _ => none) (machine w).core.k₀ (some b))
theorem column_ne_blank (b : Bool) : column w b ≠ default := by
  intro h
  have hk := congrArg (fun a : Native.Alphabet (machine w) => a.2 (machine w).core.k₀) h
  simp [column] at hk
def bottom (a : Native.Alphabet (machine w)) : Native.Alphabet (machine w) := (true,a.2)
def inclusion : PointedMap (Native.Alphabet (machine w)) (Symbol w) := ⟨Symbol.native,rfl⟩
def rawWord (word : List Bool) : List (Symbol w) := word.map Symbol.raw
def initial (word : List Bool) : Cfg w := TM0.init (rawWord w word)
def lift (c : NDPrimitiveDispatcher.Program.Cfg (machine w)) : Cfg w :=
  ⟨.inr c.q,c.Tape.map (inclusion w)⟩

def frontTable : Front → Symbol w → Option (Control w × TM0.Stmt (Symbol w))
  | .start,_ => some (.inl .putFence,.move .left)
  | .putFence,_ => some (.inl .toInput,.write .fence)
  | .toInput,_ => some (.inl .scanEnd,.move .right)
  | .scanEnd,.raw _ => some (.inl .scanEnd,.move .right)
  | .scanEnd,.native a => if a = default then some (.inl .returnLeft,.write .eof) else none
  | .returnLeft,.fence => some (.inl .backFence,.write .fence)
  | .returnLeft,_ => some (.inl .returnLeft,.move .left)
  | .skipInput,.raw b => some (.inl (.copyLeft b),.write default)
  | .skipInput,.native a => if a = default then some (.inl .skipInput,.move .right) else none
  | .skipInput,.eof => some (.inl .finishLeft,.write default)
  | .copyLeft b,.fence => some (.inl (.outLeft b),.move .left)
  | .copyLeft b,_ => some (.inl (.copyLeft b),.move .left)
  | .outLeft b,.native a => if a = default then some (.inl .backFence,.write (.native (column w b)))
      else some (.inl (.outLeft b),.move .left)
  | .backFence,.fence => some (.inl .skipInput,.move .right)
  | .backFence,_ => some (.inl .backFence,.move .right)
  | .finishLeft,.fence => some (.inl .leftStart,.write default)
  | .finishLeft,_ => some (.inl .finishLeft,.move .left)
  | .leftStart,_ => some (.inl .seekBottom,.move .left)
  | .seekBottom,.native a => if a = default then some (.inl .markBottom,.move .right)
      else some (.inl .seekBottom,.move .left)
  | .markBottom,.native a => some (.inr default,.write (.native (bottom w a)))
  | _,_ => none

def liftOpcode : TM0.Stmt (Native.Alphabet (machine w)) → TM0.Stmt (Symbol w)
  | .move d => .move d
  | .write a => .write (.native a)
def table (bit : Bool) : TM0.Machine (Symbol w) (Control w)
  | .inl state,head => frontTable w state head
  | .inr state,.native a => (Native.table (machine w) bit state a).map
      (fun result => (.inr result.1,liftOpcode w result.2))
  | .inr _,_ => none
def choose : Control w → Bool
  | .inl _ => false
  | .inr state => Native.choose (machine w) state
def step (token : Option Bool) (c : Cfg w) : Option (Cfg w) :=
  match token with
  | none => if choose w c.q then none else TM0.step (table w false) c
  | some bit => if choose w c.q then TM0.step (table w bit) c else none
structure ProgrammeData (A S : Type) [Inhabited S] where
  core : TM0.Machine A S
  alternate : TM0.Machine A S
  split : S → Bool
  main : S
abbrev Programme := ProgrammeData (Symbol w) (Control w)
def programme : Programme w := ⟨table w false,table w true,choose w,default⟩
theorem front_no_choice (s : Front) (T : Tape (Symbol w)) (bit : Bool) :
    step w (some bit) ⟨.inl s,T⟩ = none := rfl

/-- Installed native moves/writes are actual old operations through the
pointed alphabet inclusion, including blank. No simulation law is input. -/
theorem native_step (token : Option Bool) (c : NDPrimitiveDispatcher.Program.Cfg (machine w)) :
    step w token (lift w c) = (Native.step (machine w) token c).map (lift w) := by
  rcases c with ⟨state,T⟩
  cases token with
  | none =>
      cases hs : Native.choose (machine w) state
      · cases ht : Native.table (machine w) false state T.head with
        | none => simp [step,choose,lift,table,Native.step,TM0.step,hs,ht,Tape.map_fst,inclusion]
        | some result =>
          rcases result with ⟨next,operation⟩
          cases operation <;> simp [step,choose,lift,table,Native.step,TM0.step,hs,ht,liftOpcode,Tape.map_fst,Tape.map_move,Tape.map_write,inclusion]
      · simp [step,choose,lift,Native.step,hs]
  | some bit =>
      cases hs : Native.choose (machine w) state
      · simp [step,choose,lift,Native.step,hs]
      · cases ht : Native.table (machine w) bit state T.head with
        | none => simp [step,choose,lift,table,Native.step,TM0.step,hs,ht,Tape.map_fst,inclusion]
        | some result =>
          rcases result with ⟨next,operation⟩
          cases operation <;> simp [step,choose,lift,table,Native.step,TM0.step,hs,ht,liftOpcode,Tape.map_fst,Tape.map_move,Tape.map_write,inclusion]

end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.NDPrimitiveFrontend.Program
