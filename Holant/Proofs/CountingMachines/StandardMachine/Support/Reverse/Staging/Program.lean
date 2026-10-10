import Holant.Proofs.CountingMachines.StandardMachine.Support.Reverse.Staging.Cleanup
import Holant.Proofs.CountingMachines.VerifierCircuit.Support.Polynomial

set_option backward.isDefEq.respectTransparency false
/-! Adapted reference proof. See the task validation reports. Whole finite wrapper code, beginning on the original
tagged single input tape. It scans and reverses both fields, physically computes
the prescribed polynomial clock, executes the unchanged packet interpreter,
checks simultaneous clock/packet EOF and original halt/accept control, then
erases every heterogeneous tape and returns one tagged Bool with reset state.
No mathematical decoding/evaluation/configuration operation is an opcode. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Reverse.Staging.Program
open Turing Holant.Complexity BinaryCompose
attribute [local instance] Classical.propDecidable
open Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support

variable (m : BinaryMachine) (T : Polynomial ℕ)
local instance : Fintype m.core.K := m.core.kFin
local instance : Fintype m.core.Λ := m.core.ΛFin
local instance : Fintype m.core.σ := m.core.σFin
local instance (k : m.core.K) : Fintype (m.core.Γ k) := m.alphabets k

def clockComputes (T : Polynomial ℕ) := Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.RuntimeParameters.polynomialComputes T
abbrev clock := (clockComputes T).machine
abbrev Extra := Unit ⊕ (Unit ⊕ Unit)
def ExtraAlphabet : Extra → Type
  | .inl _ => m.core.Γ m.core.k₀ ⊕ Bool
  | .inr (.inl _) => m.core.Γ m.core.k₀
  | .inr (.inr _) => Bool
abbrev InnerStack := Extra ⊕ Reverse.Program.Stack m
abbrev InnerAlphabet := HeterogeneousSum.Alphabet (ExtraAlphabet m) (Reverse.Program.Alphabet m)
abbrev Stack := (clock T).K ⊕ InnerStack m
abbrev Alphabet : Stack m T → Type := SumStacks.Alphabet (InnerAlphabet m)
abbrev State := (clock T).State × Option (m.core.Γ m.core.k₀ ⊕ Bool) ×
  Option (m.core.Γ m.core.k₀) × Option Bool × Bool × Bool × Reverse.Program.State m
abbrev Label := (clock T).Label ⊕
  (Fin 3 ⊕ (Reverse.Program.Label m ⊕ Cleanup.Label (K := Stack m T)))

def raw : Stack m T := .inr (.inl (.inl ()))
def originalBuffer : Stack m T := .inr (.inl (.inr (.inl ())))
def packetBuffer : Stack m T := .inr (.inl (.inr (.inr ())))
def packet : Stack m T := .inr (.inr (.inl ()))
def originalInput : Stack m T := .inr (.inr (.inr m.core.k₀))
def counter : Stack m T := .inl (clock T).output
def scanner (i : Fin 3) : Label m T := .inr (.inl i)
def interpreter (l : Reverse.Program.Label m) : Label m T := .inr (.inr (.inl l))
def clean (i : Cleanup.Label (K := Stack m T)) : Label m T := .inr (.inr (.inr i))
def initial : State m T :=
  ((clock T).initial,none,none,none,false,false,Reverse.Program.clear m m.core.initialState)

def setRaw (v : State m T) (x : Option (m.core.Γ m.core.k₀ ⊕ Bool)) : State m T :=
  (v.1,x,v.2.2)
def setOriginal (v : State m T) (x : Option (m.core.Γ m.core.k₀)) : State m T :=
  (v.1,v.2.1,x,v.2.2.2)
def setBit (v : State m T) (x : Option Bool) : State m T :=
  (v.1,v.2.1,v.2.2.1,x,v.2.2.2.2)
def setSeen (v : State m T) (x : Bool) : State m T :=
  (v.1,v.2.1,v.2.2.1,v.2.2.2.1,x,v.2.2.2.2.2)
def setVerdict (v : State m T) (x : Bool) : State m T :=
  (v.1,v.2.1,v.2.2.1,v.2.2.2.1,v.2.2.2.2.1,x,v.2.2.2.2.2.2)
def oldState (v : State m T) : Reverse.Program.State m := v.2.2.2.2.2.2
def resetScratch (v : State m T) : State m T :=
  (v.1,none,none,none,v.2.2.2.2.1,v.2.2.2.2.2.1,oldState m T v)

def oldStates : StateEmbedding (Reverse.Program.State m) (State m T) where
  put v := ((clock T).initial,none,none,none,false,false,v)
  get := oldState m T
  get_put _ := rfl

def clockStates : StateEmbedding (clock T).State (State m T) where
  put v := (v,none,none,none,false,false,Reverse.Program.clear m m.core.initialState)
  get := Prod.fst
  get_put _ := rfl

def clockLayout : StackEmbedding (clock T).K (clock T).K where
  key := id
  lift := id
  lookup _ _ := rfl
  update _ _ _ := rfl

def cleanupStates : StateEmbedding Cleanup.State (State m T) where
  put v := setVerdict m T (setSeen m T (initial m T) v.1) v.2
  get v := (v.2.2.2.2.1,v.2.2.2.2.2.1)
  get_put _ := rfl

def finish (verdict : State m T → Bool) : TM2.Stmt (Alphabet m T) (Label m T) (State m T) :=
  .load (fun v => (cleanupStates m T).put (false,verdict v)) (.goto (fun _ => clean m T 0))

def oldStatement (q : (Reverse.Program.computer m).Stmt) :
    TM2.Stmt (Alphabet m T) (Label m T) (State m T) :=
  HeterogeneousSum.rightStmt (fun _ : (clock T).K => Bool) (InnerAlphabet m)
    (oldStates m T) (interpreter m T) none
      (HeterogeneousSum.rightStmt (ExtraAlphabet m) (Reverse.Program.Alphabet m)
        ⟨id,id,fun _ => rfl⟩ id none q)

/-- Empty source input alphabets are allowed. A fixed construction-time
nonempty test only installs the push arm if an actual symbol can exist. -/
def pushOriginal (destination : Stack m T)
    (same : Alphabet m T destination = m.core.Γ m.core.k₀)
    (get : State m T → Option (m.core.Γ m.core.k₀))
    (next : Label m T) : TM2.Stmt (Alphabet m T) (Label m T) (State m T) :=
  if h : Nonempty (m.core.Γ m.core.k₀) then
    .push destination (fun v => same.symm ▸ ((get v).getD (Classical.choice h)))
      (.load (resetScratch m T) (.goto (fun _ => next)))
  else finish m T (fun _ => false)

def rawLeft : State m T → Option (m.core.Γ m.core.k₀)
  | (_,some (.inl a),_) => some a
  | _ => none
def rawRight : State m T → Bool
  | (_,some (.inr b),_) => b
  | _ => false

/-- The source accepting-control table is model data. It is consulted only
when both physical EOF tests succeeded and the same original label is none. -/
def program (acceptControl : m.core.σ → Bool) :
    Label m T → TM2.Stmt (Alphabet m T) (Label m T) (State m T)
  | .inl l => SumStacks.leftStmt (InnerAlphabet m)
      (embedStmt (clockLayout T) (clockStates m T) Sum.inl
        (some (interpreter m T (Reverse.Program.label m (some m.core.main) 0))) ((clock T).program l))
  | .inr (.inl i) =>
      if i = 0 then
        .pop (raw m T) (setRaw m T)
          (.branch (fun v => v.2.1.isSome)
            (.branch (fun v => (rawLeft m T v).isSome)
              (.branch (fun v => v.2.2.2.2.1)
                (finish m T (fun _ => false))
                (.push (.inl (clock T).input) (fun _ => true)
                  (pushOriginal m T (originalBuffer m T) rfl (rawLeft m T) (scanner m T 0))))
              (.push (packetBuffer m T) (rawRight m T)
                (.load (fun v => resetScratch m T (setSeen m T v true))
                  (.goto (fun _ => scanner m T 0)))))
            (.load (resetScratch m T) (.goto (fun _ => scanner m T 1))))
      else if i = 1 then
        .pop (originalBuffer m T) (setOriginal m T)
          (.branch (fun v => v.2.2.1.isSome)
            (pushOriginal m T (originalInput m T) rfl (fun v => v.2.2.1) (scanner m T 1))
            (.load (resetScratch m T) (.goto (fun _ => scanner m T 2))))
      else .pop (packetBuffer m T) (setBit m T)
        (.branch (fun v => v.2.2.2.1.isSome)
          (.push (packet m T) (fun v => v.2.2.2.1.getD false)
            (.load (resetScratch m T) (.goto (fun _ => scanner m T 2))))
          (.load (fun _ => initial m T) (.goto (fun _ => .inl (clock T).main))))
  | .inr (.inr (.inl (.inl _))) => finish m T (fun _ => false)
  | .inr (.inr (.inl l@(.inr (source,phase)))) =>
      if phase = 0 then
        .pop (counter m T) (setBit m T)
          (.branch (fun v => v.2.2.2.1.isSome)
            (oldStatement m T (Reverse.Program.program m l))
            (.peek (packet m T) (setBit m T)
              (finish m T (fun v =>
                !v.2.2.2.1.isSome && source.isNone && acceptControl (oldState m T v).2.2))))
      else oldStatement m T (Reverse.Program.program m l)
  | .inr (.inr (.inr i)) =>
      HeterogeneousSum.restateStmt (Alphabet m T) (cleanupStates m T) (clean m T) none
        (Cleanup.program (Alphabet m T) (raw m T) Sum.inr i)

def computer (acceptControl : m.core.σ → Bool) : FinTM2 where
  K := Stack m T
  k₀ := raw m T
  k₁ := raw m T
  Γ := Alphabet m T
  Γk₀Fin := inferInstanceAs (Fintype (m.core.Γ m.core.k₀ ⊕ Bool))
  Λ := Label m T
  main := scanner m T 0
  σ := State m T
  initialState := initial m T
  m := program m T acceptControl

def deterministic (acceptControl : m.core.σ → Bool) : BinaryMachine where
  core := computer m T acceptControl
  alternate := program m T acceptControl
  split _ := false
  alphabets key := by
    cases key with
    | inl k => exact inferInstanceAs (Fintype Bool)
    | inr k =>
      cases k with
      | inl k =>
        cases k with
        | inl u => exact inferInstanceAs (Fintype (m.core.Γ m.core.k₀ ⊕ Bool))
        | inr k =>
          cases k with
          | inl _ => exact m.alphabets m.core.k₀
          | inr _ => exact inferInstanceAs (Fintype Bool)
      | inr k =>
        cases k with
        | inl u => exact inferInstanceAs (Fintype Bool)
        | inr k => exact m.alphabets k

end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Reverse.Staging.Program
