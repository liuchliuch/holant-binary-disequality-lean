import Holant.Proofs.CountingMachines.StandardMachine.Support.BooleanOpcode.Resources

set_option backward.isDefEq.respectTransparency false
/-! Locally checked adaptation of the frozen reference proof. Physical preparation on original native Boolean input
bytes. Each original byte is read once and emits fixed code bits into a real
reversal buffer; a second real pop/push loop restores the complete coded input.
The codec equivalence below is finite alphabet metadata, not an input execution
or count law. General finite raw alphabets need a separate raw serialization
boundary; this native input producer does not claim that missing consumer. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.BooleanOpcode.NativeInput
open Turing Computability Holant.Complexity BinaryCompose
variable (m : BinaryMachine) (inputAlphabet : m.core.Γ m.core.k₀ ≃ Bool)
local instance : Fintype m.core.K := m.core.kFin
local instance : Fintype m.core.Λ := m.core.ΛFin
local instance : Fintype m.core.σ := m.core.σFin
abbrev Stack := Unit ⊕ (Unit ⊕ m.core.K)
abbrev Label := Fin 2 ⊕ m.core.Λ
abbrev State := Block.State m
def raw : Stack m := .inl ()
def buffer : Stack m := .inr (.inl ())
def source (k : m.core.K) : Stack m := .inr (.inr k)
def tapes (word temporary : List Bool) (S : m.core.K → List Bool) : Stack m → List Bool
  | .inl _ => word
  | .inr (.inl _) => temporary
  | .inr (.inr k) => S k

@[simp] theorem tapes_raw (word temporary : List Bool) (S : m.core.K → List Bool) :
    tapes m word temporary S (raw m) = word := rfl
@[simp] theorem tapes_buffer (word temporary : List Bool) (S : m.core.K → List Bool) :
    tapes m word temporary S (buffer m) = temporary := rfl
@[simp] theorem tapes_source (word temporary : List Bool) (S : m.core.K → List Bool) (k : m.core.K) :
    tapes m word temporary S (source m k) = S k := rfl

theorem update_raw (word temporary : List Bool) (S : m.core.K → List Bool) (rest : List Bool) :
    Function.update (tapes m word temporary S) (raw m) rest = tapes m rest temporary S := by
  funext k
  cases k with
  | inl u => cases u; rfl
  | inr k => cases k <;> simp [tapes,raw]
theorem update_buffer (word temporary : List Bool) (S : m.core.K → List Bool) (rest : List Bool) :
    Function.update (tapes m word temporary S) (buffer m) rest = tapes m word rest S := by
  funext k
  cases k with
  | inl u => simp [tapes,buffer]
  | inr k => cases k with
    | inl u => cases u; rfl
    | inr k => simp [tapes,buffer]
theorem update_source (word temporary : List Bool) (S : m.core.K → List Bool)
    (k : m.core.K) (rest : List Bool) :
    Function.update (tapes m word temporary S) (source m k) rest =
      tapes m word temporary (Function.update S k rest) := by
  funext j
  cases j with
  | inl u => simp [tapes,source]
  | inr j => cases j with
    | inl u => simp [tapes,source]
    | inr j => by_cases hj : j = k <;> simp [tapes,source,hj]

def layout : StackEmbedding m.core.K (Stack m) where
  key := source m
  lift := tapes m [] []
  lookup _ _ := rfl
  update := update_source m [] []
def states : StateEmbedding (State m) (State m) := ⟨id,id,fun _ => rfl⟩

/-- Push in chronological bit order, hence reverse the emitted code on tape.
Only fixed finite functions producing one Bool occur in the syntax. -/
def pushForward (key : Stack m) : (n : ℕ) → (Fin n → State m → Bool) →
    TM2.Stmt (fun _ : Stack m => Bool) (Label m) (State m) →
    TM2.Stmt (fun _ : Stack m => Bool) (Label m) (State m)
  | 0,_,next => next
  | n+1,bits,next => .push key (bits 0) (pushForward key n (fun i => bits i.succ) next)

theorem pushForward_eval (key : Stack m) (n : ℕ) (bits : Fin n → State m → Bool)
    (next : TM2.Stmt (fun _ : Stack m => Bool) (Label m) (State m))
    (v : State m) (S : Stack m → List Bool) :
    TM2.stepAux (pushForward m key n bits next) v S = TM2.stepAux next v
      (Function.update S key ((List.ofFn (fun i => bits i v)).reverse++S key)) := by
  induction n generalizing next S with
  | zero => simp [pushForward]
  | succ n ih =>
    rw [pushForward,TM2.stepAux,ih,List.ofFn_succ,List.reverse_cons]
    simp only [Function.update_self,Function.update_idem,List.append_assoc,List.singleton_append]

def program (alternate : Bool) : Label m → TM2.Stmt (fun _ : Stack m => Bool) (Label m) (State m)
  | .inl i => if i = 0 then
      .pop (raw m) (Block.setBit m)
        (.branch (fun v => v.2.1.isSome)
          (pushForward m (buffer m) (Code.width m m.core.k₀)
            (fun j v => Code.bit m m.core.k₀ (inputAlphabet.symm (v.2.1.getD false)) j)
            (.load (fun _ => Block.clear m m.core.initialState) (.goto (fun _ => .inl 0))))
          (.load (fun _ => Block.clear m m.core.initialState) (.goto (fun _ => .inl 1))))
    else .pop (buffer m) (Block.setBit m)
      (.branch (fun v => v.2.1.isSome)
        (.push (source m m.core.k₀) (fun v => v.2.1.getD false)
          (.load (fun _ => Block.clear m m.core.initialState) (.goto (fun _ => .inl 1))))
        (.load (fun _ => Block.clear m m.core.initialState) (.goto (fun _ => .inr m.core.main))))
  | .inr l => embedStmt (layout m) (states m) Sum.inr none
      (Compiler.statement m (if alternate then m.alternate l else m.core.m l))

abbrev computer : FinTM2 where
  K := Stack m
  k₀ := raw m
  k₁ := source m m.core.k₁
  Γ := fun _ => Bool
  Λ := Label m
  main := .inl 0
  σ := State m
  initialState := Block.clear m m.core.initialState
  m := program m inputAlphabet false
abbrev machine : BinaryMachine where
  core := computer m inputAlphabet
  alternate := program m inputAlphabet true
  split
    | .inl _ => false
    | .inr l => m.split l
  alphabets _ := inferInstance

def scanCfg (word temporary : List Bool) : (machine m inputAlphabet).Config :=
  ⟨some (.inl 0),Block.clear m m.core.initialState,tapes m word temporary (fun _ => [])⟩
def moveCfg (temporary word : List Bool) : (machine m inputAlphabet).Config :=
  ⟨some (.inl 1),Block.clear m m.core.initialState,
    tapes m [] temporary (Function.update (fun _ => []) m.core.k₀ word)⟩
def sourceCfg (c : (Compiler.machine m).Config) : (machine m inputAlphabet).Config :=
  embedCfg (layout m) (states m) Sum.inr none c

theorem scan_cons (b : Bool) (rest temporary : List Bool) (log : List Bool) :
    (machine m inputAlphabet).advance (log,scanCfg m inputAlphabet (b::rest) temporary) =
      some (log,scanCfg m inputAlphabet rest
        ((Code.symbol m m.core.k₀ (inputAlphabet.symm b)).reverse++temporary)) := by
  simp only [BinaryMachine.advance,BinaryMachine.step,machine,computer,scanCfg,
    program,Bool.false_eq_true,if_false,if_true,TM2.stepAux,tapes_raw,
    Block.setBit,List.head?_cons,List.tail_cons,Option.isSome_some,Option.getD_some]
  rw [update_raw,pushForward_eval,update_buffer]
  rfl

theorem scan_nil (temporary : List Bool) (log : List Bool) :
    (machine m inputAlphabet).advance (log,scanCfg m inputAlphabet [] temporary) =
      some (log,moveCfg m inputAlphabet temporary []) := by
  simp [BinaryMachine.advance,BinaryMachine.step,machine,computer,scanCfg,moveCfg,
    program,TM2.stepAux,tapes_raw,Block.setBit,update_raw]

theorem move_cons (b : Bool) (rest word : List Bool) (log : List Bool) :
    (machine m inputAlphabet).advance (log,moveCfg m inputAlphabet (b::rest) word) =
      some (log,moveCfg m inputAlphabet rest (b::word)) := by
  simp [BinaryMachine.advance,BinaryMachine.step,machine,computer,moveCfg,program,
    TM2.stepAux,tapes_buffer,tapes_source,Block.setBit,update_buffer,update_source,Function.update_idem]

theorem move_nil (word : List Bool) (log : List Bool) :
    (machine m inputAlphabet).advance (log,moveCfg m inputAlphabet [] word) =
      some (log,sourceCfg m inputAlphabet (initList (Compiler.computer m) word)) := by
  have hu : Function.update (fun _ : m.core.K => ([] : List Bool)) m.core.k₀ word =
      (fun k => if k = m.core.k₀ then word else []) := by
    funext k
    simp [Function.update_apply]
  simp [BinaryMachine.advance,BinaryMachine.step,machine,computer,moveCfg,sourceCfg,
    program,TM2.stepAux,tapes_buffer,tapes_source,Block.setBit,update_buffer,embedCfg,layout,states,
    initList,Compiler.computer,hu]

theorem scan_run (word temporary : List Bool) (log : List Bool) :
    (machine m inputAlphabet).run (word.length+1) (log,scanCfg m inputAlphabet word temporary) =
      some (log,moveCfg m inputAlphabet
        ((Code.word m m.core.k₀ (word.map inputAlphabet.symm)).reverse++temporary) []) := by
  induction word generalizing temporary with
  | nil => simpa [Code.word,BinaryMachine.run] using scan_nil m inputAlphabet temporary log
  | cons b word ih =>
    rw [List.length_cons,BinaryMachine.run,scan_cons,Option.bind_some,ih]
    simp only [List.map_cons,Code.word,List.flatMap_cons,List.reverse_append,List.append_assoc]

theorem move_run (temporary word : List Bool) (log : List Bool) :
    (machine m inputAlphabet).run (temporary.length+1) (log,moveCfg m inputAlphabet temporary word) =
      some (log,sourceCfg m inputAlphabet
        (initList (Compiler.computer m) (temporary.reverse++word))) := by
  induction temporary generalizing word with
  | nil => simpa [BinaryMachine.run] using move_nil m inputAlphabet word log
  | cons b temporary ih =>
    rw [List.length_cons,BinaryMachine.run,move_cons,Option.bind_some,ih]
    simp only [List.reverse_cons,List.append_assoc,List.singleton_append]

def steps (n : ℕ) : ℕ := (Code.width m m.core.k₀+1)*n+2

/-- Original raw bytes are physically consumed and coded on work stacks.
The producer returns the same source init with no raw or reversal residue. -/
theorem prepare (word : List Bool) (log : List Bool) :
    (machine m inputAlphabet).run (steps m word.length)
      (log,initList (computer m inputAlphabet) word) =
        some (log,sourceCfg m inputAlphabet
          (Compiler.cfg m (initList m.core (word.map inputAlphabet.symm)))) := by
  have hi : initList (computer m inputAlphabet) word = scanCfg m inputAlphabet word [] := by
    change (⟨_,_,_⟩ : (machine m inputAlphabet).Config) = ⟨_,_,_⟩
    congr 1
    funext k
    cases k with
    | inl u => cases u; simp [computer,scanCfg,initList,tapes,raw]
    | inr k => cases k <;> simp [computer,scanCfg,initList,tapes,raw]
  have hs := scan_run m inputAlphabet word [] log
  have hm := move_run m inputAlphabet
    (Code.word m m.core.k₀ (word.map inputAlphabet.symm)).reverse [] log
  rw [hi,show steps m word.length =
      ((Code.word m m.core.k₀ (word.map inputAlphabet.symm)).reverse.length+1)+(word.length+1) by
        simp only [steps,List.length_reverse,Code.word_length,List.length_map,Nat.add_mul,Nat.one_mul]
        omega,BinaryMachine.run_add,hs,Option.bind_some]
  simpa only [List.append_nil,List.reverse_reverse,Compiler.cfg_init] using hm

theorem pushForward_budget (key : Stack m) (n : ℕ) (bits : Fin n → State m → Bool)
    (next : TM2.Stmt (fun _ : Stack m => Bool) (Label m) (State m)) :
    HeterogeneousCost.budget (pushForward m key n bits next) = n+HeterogeneousCost.budget next := by
  induction n generalizing next with
  | zero => simp [pushForward]
  | succ n ih => simp [pushForward,HeterogeneousCost.budget,ih,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.BooleanOpcode.NativeInput
