import Holant.Proofs.CountingMachines.StandardMachine.Support.BooleanOpcode.Source

set_option backward.isDefEq.respectTransparency false
/-! Locally checked adaptation of the frozen reference proof. Real Boolean-stack frontend for an arbitrary finite
source input alphabet. A fixed-depth literal block reader emits each validated
symbol's reversed code and one unary length token. Real bit-copy and length
clear loops then enter the same compiled source with all new stacks empty.
The metadata machine below supplies a finite alphabet/table to the old reader;
it is never executed. No whole-word decoder or input length is an opcode. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.GeneralAlphabetInput.Program
open Turing Computability Holant.Complexity BinaryCompose
open Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.BooleanOpcode
variable (b : BinaryMachine)
local instance : Fintype b.core.K := b.core.kFin
local instance : Fintype b.core.Λ := b.core.ΛFin
local instance : Fintype b.core.σ := b.core.σFin
local instance (k : b.core.K) : Fintype (b.core.Γ k) := b.alphabets k
abbrev Stack := Unit ⊕ (Unit ⊕ (Unit ⊕ b.core.K))
abbrev Label := Fin 3 ⊕ b.core.Λ
def raw : Stack b := .inl ()
def buffer : Stack b := .inr (.inl ())
def counter : Stack b := .inr (.inr (.inl ()))
def source (k : b.core.K) : Stack b := .inr (.inr (.inr k))
def Alphabet : Stack b → Type
  | .inl _ => b.core.Γ b.core.k₀
  | .inr (.inl _) => Bool
  | .inr (.inr (.inl _)) => Bool
  | .inr (.inr (.inr k)) => b.core.Γ k
local instance (k : Stack b) : Fintype (Alphabet b k) := by
  cases k with
  | inl _ => exact b.alphabets b.core.k₀
  | inr k => cases k with
    | inl _ => exact Bool.fintype
    | inr k => cases k with
      | inl _ => exact Bool.fintype
      | inr k => exact b.alphabets k

/-- Compile-time finite metadata for Block.readSymbol, with the SAME input
alphabet enumeration as b. All actual runtime tapes below are Bool. -/
def metadata : BinaryMachine where
  core := {
    K := Stack b
    k₀ := raw b
    k₁ := source b b.core.k₁
    Γ := Alphabet b
    Λ := Label b
    main := .inl 0
    σ := b.core.σ
    initialState := b.core.initialState
    m := fun _ => .halt }
  alternate := fun _ => .halt
  split := fun _ => false
  alphabets _ := inferInstance
abbrev State := Block.State (metadata b)
theorem raw_width : Code.width (metadata b) (raw b) = Code.width b b.core.k₀ := rfl
theorem raw_symbol (a : b.core.Γ b.core.k₀) :
    Code.symbol (metadata b) (raw b) a = Code.symbol b b.core.k₀ a := rfl

def tapes (word temporary length : List Bool) (S : b.core.K → List Bool) : Stack b → List Bool
  | .inl _ => word
  | .inr (.inl _) => temporary
  | .inr (.inr (.inl _)) => length
  | .inr (.inr (.inr k)) => S k
@[simp] theorem tapes_raw (word temporary length : List Bool) (S : b.core.K → List Bool) :
    tapes b word temporary length S (raw b) = word := rfl
@[simp] theorem tapes_buffer (word temporary length : List Bool) (S : b.core.K → List Bool) :
    tapes b word temporary length S (buffer b) = temporary := rfl
@[simp] theorem tapes_counter (word temporary length : List Bool) (S : b.core.K → List Bool) :
    tapes b word temporary length S (counter b) = length := rfl
@[simp] theorem tapes_source (word temporary length : List Bool) (S : b.core.K → List Bool) (k : b.core.K) :
    tapes b word temporary length S (source b k) = S k := rfl
theorem update_raw (word temporary length : List Bool) (S : b.core.K → List Bool) (rest : List Bool) :
    Function.update (tapes b word temporary length S) (raw b) rest = tapes b rest temporary length S := by
  funext k
  cases k with
  | inl u => cases u; rfl
  | inr k => cases k with
    | inl _ => simp [tapes,raw]
    | inr k => cases k <;> simp [tapes,raw]
theorem update_buffer (word temporary length : List Bool) (S : b.core.K → List Bool) (rest : List Bool) :
    Function.update (tapes b word temporary length S) (buffer b) rest = tapes b word rest length S := by
  funext k
  cases k with
  | inl _ => simp [tapes,buffer]
  | inr k => cases k with
    | inl u => cases u; rfl
    | inr k => cases k <;> simp [tapes,buffer]
theorem update_counter (word temporary length : List Bool) (S : b.core.K → List Bool) (rest : List Bool) :
    Function.update (tapes b word temporary length S) (counter b) rest = tapes b word temporary rest S := by
  funext k
  cases k with
  | inl _ => simp [tapes,counter]
  | inr k => cases k with
    | inl _ => simp [tapes,counter]
    | inr k => cases k with
      | inl u => cases u; rfl
      | inr k => simp [tapes,counter]
theorem update_source (word temporary length : List Bool) (S : b.core.K → List Bool)
    (key : b.core.K) (rest : List Bool) :
    Function.update (tapes b word temporary length S) (source b key) rest =
      tapes b word temporary length (Function.update S key rest) := by
  funext k
  cases k with
  | inl _ => simp [tapes,source]
  | inr k => cases k with
    | inl _ => simp [tapes,source]
    | inr k => cases k with
      | inl _ => simp [tapes,source]
      | inr k => by_cases hk : k = key <;> simp [tapes,source,hk]
def layout : StackEmbedding b.core.K (Stack b) where
  key := source b
  lift := tapes b [] [] []
  lookup _ _ := rfl
  update := update_source b [] [] []
def states : StateEmbedding (Compiler.State b) (State b) := ⟨id,id,fun _ => rfl⟩

/-- Every leaf's a is a fixed symbol of the construction-time decision tree.
Fin.rev selects a fixed bit; the runtime function ignores its finite state. -/
def scanLeaf (head : Option (b.core.Γ b.core.k₀)) :
    TM2.Stmt (fun _ : Stack b => Bool) (Label b) (State b) :=
  head.elim
    (.load (fun _ => Block.clear (metadata b) b.core.initialState) (.goto (fun _ => .inl 1)))
    (fun a => Block.pushVector (metadata b) (buffer b) (Code.width b b.core.k₀)
      (fun i _ => Code.bit b b.core.k₀ a i.rev)
      (.push (counter b) (fun _ => true)
        (.load (fun _ => Block.clear (metadata b) b.core.initialState) (.goto (fun _ => .inl 0)))))
def program (alternate : Bool) : Label b → TM2.Stmt (fun _ : Stack b => Bool) (Label b) (State b)
  | .inl i => if i = 0 then Block.readSymbol (metadata b) (raw b) (scanLeaf b)
    else if i = 1 then .pop (buffer b) (Block.setBit (metadata b))
      (.branch (fun v => v.2.1.isSome)
        (.push (source b b.core.k₀) (fun v => v.2.1.getD false)
          (.load (fun _ => Block.clear (metadata b) b.core.initialState) (.goto (fun _ => .inl 1))))
        (.load (fun _ => Block.clear (metadata b) b.core.initialState) (.goto (fun _ => .inl 2))))
    else .pop (counter b) (Block.setBit (metadata b))
      (.branch (fun v => v.2.1.isSome)
        (.load (fun _ => Block.clear (metadata b) b.core.initialState) (.goto (fun _ => .inl 2)))
        (.load (fun _ => Block.clear (metadata b) b.core.initialState) (.goto (fun _ => .inr b.core.main))))
  | .inr l => embedStmt (layout b) (states b) Sum.inr none
      (Compiler.statement b (if alternate then b.alternate l else b.core.m l))
abbrev computer : FinTM2 where
  K := Stack b
  k₀ := raw b
  k₁ := source b b.core.k₁
  Γ := fun _ => Bool
  Λ := Label b
  main := .inl 0
  σ := State b
  initialState := Block.clear (metadata b) b.core.initialState
  m := program b false
abbrev machine : BinaryMachine where
  core := computer b
  alternate := program b true
  split
    | .inl _ => false
    | .inr l => b.split l
  alphabets _ := inferInstance
def scanCfg (word temporary length : List Bool) : (machine b).Config :=
  ⟨some (.inl 0),Block.clear (metadata b) b.core.initialState,tapes b word temporary length (fun _ => [])⟩
def moveCfg (temporary length word : List Bool) : (machine b).Config :=
  ⟨some (.inl 1),Block.clear (metadata b) b.core.initialState,
    tapes b [] temporary length (Function.update (fun _ => []) b.core.k₀ word)⟩
def clearCfg (length word : List Bool) : (machine b).Config :=
  ⟨some (.inl 2),Block.clear (metadata b) b.core.initialState,
    tapes b [] [] length (Function.update (fun _ => []) b.core.k₀ word)⟩
def readyCfg (c : (Compiler.machine b).Config) : (machine b).Config :=
  embedCfg (layout b) (states b) Sum.inr none c

/-- The same installed source table, including both genuine split arms and
the sole held halt edge. Preparation introduces no new branch labels. -/
theorem source_step (token : Option Bool) (c : (Compiler.machine b).Config) :
    (machine b).step token (readyCfg b c) =
      ((Compiler.machine b).step token c).map (readyCfg b) := by
  cases hl : c.l with
  | none => cases token <;> simp [BinaryMachine.step,readyCfg,embedCfg,hl]
  | some l =>
    cases token with
    | none => cases hs : b.split l <;>
        simp [BinaryMachine.step,readyCfg,embedCfg,hl,machine,computer,program,
          Compiler.machine,Compiler.computer,hs,embed_stepAux]
    | some choice => cases choice <;> cases hs : b.split l <;>
        simp [BinaryMachine.step,readyCfg,embedCfg,hl,machine,computer,program,
          Compiler.machine,Compiler.computer,hs,embed_stepAux]

/-- Ordinary source execution uses the existing structural instruction
producer. There is no callback that executes a whole source configuration. -/
theorem source_core_step (c d : (Compiler.machine b).Config)
    (h : (Compiler.computer b).step c = some d) :
    (computer b).step (readyCfg b c) = some (readyCfg b d) :=
  embed_step (layout b) (states b) Sum.inr none
    (Compiler.computer b).m (computer b).m (fun _ => rfl) c d h

theorem reversed_code (a : b.core.Γ b.core.k₀) :
    List.ofFn (fun i : Fin (Code.width b b.core.k₀) => Code.bit b b.core.k₀ a i.rev) =
      (Code.symbol b b.core.k₀ a).reverse := by
  apply List.ext_getElem
  · simp [Code.symbol]
  · intro i hi hj
    simp only [Code.symbol,List.getElem_ofFn,List.getElem_reverse,List.length_ofFn]
    apply congrArg (Code.bit b b.core.k₀ a)
    apply Fin.ext
    simp only [Fin.rev]
    omega

theorem scan_symbol (a : b.core.Γ b.core.k₀) (rest temporary length : List Bool) (log : List Bool) :
    (machine b).advance (log,scanCfg b (Code.symbol b b.core.k₀ a++rest) temporary length) =
      some (log,scanCfg b rest ((Code.symbol b b.core.k₀ a).reverse++temporary) (true::length)) := by
  have hr : tapes b (Code.symbol b b.core.k₀ a++rest) temporary length (fun _ => []) =
      Function.update (tapes b rest temporary length (fun _ => [])) (raw b)
        (Code.symbol (metadata b) (raw b) a++tapes b rest temporary length (fun _ => []) (raw b)) := by
    rw [raw_symbol,update_raw,tapes_raw]
  simp only [BinaryMachine.advance,BinaryMachine.step,machine,computer,scanCfg,program,
    Bool.false_eq_true,if_false,if_true]
  rw [hr,Block.read_symbol]
  simp only [scanLeaf,Option.elim_some]
  rw [Block.pushVector_eval,reversed_code,update_buffer]
  simp [TM2.stepAux,update_counter b,Block.clear]

theorem scan_empty (temporary length log : List Bool) :
    (machine b).advance (log,scanCfg b [] temporary length) = some (log,moveCfg b temporary length []) := by
  have he : tapes b [] temporary length (fun _ => []) (raw b) = [] := rfl
  simp only [BinaryMachine.advance,BinaryMachine.step,machine,computer,scanCfg,program,
    Bool.false_eq_true,if_false,if_true]
  rw [Block.read_empty _ _ _ _ _ he]
  simp [scanLeaf,TM2.stepAux,moveCfg,Block.clear]
theorem move_symbol (bit : Bool) (rest length word log : List Bool) :
    (machine b).advance (log,moveCfg b (bit::rest) length word) =
      some (log,moveCfg b rest length (bit::word)) := by
  simp [BinaryMachine.advance,BinaryMachine.step,machine,computer,moveCfg,program,TM2.stepAux,
    tapes_buffer,tapes_source,Block.setBit,update_buffer,update_source,Function.update_idem]
theorem move_empty (length word log : List Bool) :
    (machine b).advance (log,moveCfg b [] length word) = some (log,clearCfg b length word) := by
  simp [BinaryMachine.advance,BinaryMachine.step,machine,computer,moveCfg,clearCfg,program,
    TM2.stepAux,tapes_buffer,tapes_source,Block.setBit,update_buffer]
theorem clear_symbol (bit : Bool) (rest word log : List Bool) :
    (machine b).advance (log,clearCfg b (bit::rest) word) = some (log,clearCfg b rest word) := by
  simp [BinaryMachine.advance,BinaryMachine.step,machine,computer,clearCfg,program,
    TM2.stepAux,tapes_counter,Block.setBit,update_counter]
theorem clear_empty (word log : List Bool) :
    (machine b).advance (log,clearCfg b [] word) =
      some (log,readyCfg b (initList (Compiler.computer b) word)) := by
  simp [BinaryMachine.advance,BinaryMachine.step,machine,computer,clearCfg,readyCfg,program,
    TM2.stepAux,tapes_counter,Block.setBit,update_counter,embedCfg,layout,states,initList,Compiler.computer,Block.clear]
  congr 1
  congr 1
  funext k
  simp [Function.update_apply]

theorem replicate_counter (n : ℕ) (length : List Bool) :
    List.replicate n true++(true::length) = List.replicate (n+1) true++length := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [List.replicate_succ,List.cons_append] using congrArg (true::·) ih

theorem scan_run (word : List (b.core.Γ b.core.k₀)) (temporary length log : List Bool) :
    (machine b).run (word.length+1) (log,scanCfg b (Code.word b b.core.k₀ word) temporary length) =
      some (log,moveCfg b ((Code.word b b.core.k₀ word).reverse++temporary)
        (List.replicate word.length true++length) []) := by
  induction word generalizing temporary length with
  | nil => simpa [Code.word,BinaryMachine.run] using scan_empty b temporary length log
  | cons a word ih =>
    have hword : Code.word b b.core.k₀ (a::word) = Code.symbol b b.core.k₀ a ++ Code.word b b.core.k₀ word := rfl
    rw [List.length_cons,BinaryMachine.run,hword,scan_symbol,Option.bind_some,ih]
    simp [Code.word,List.reverse_append,replicate_counter,List.append_assoc]
theorem move_run (temporary length word log : List Bool) :
    (machine b).run (temporary.length+1) (log,moveCfg b temporary length word) =
      some (log,clearCfg b length (temporary.reverse++word)) := by
  induction temporary generalizing word with
  | nil => simpa [BinaryMachine.run] using move_empty b length word log
  | cons bit temporary ih =>
    rw [List.length_cons,BinaryMachine.run,move_symbol,Option.bind_some,ih]
    simp [List.reverse_cons,List.append_assoc]
theorem clear_run (length word log : List Bool) :
    (machine b).run (length.length+1) (log,clearCfg b length word) =
      some (log,readyCfg b (initList (Compiler.computer b) word)) := by
  induction length with
  | nil => simpa [BinaryMachine.run] using clear_empty b word log
  | cons bit length ih => rw [List.length_cons,BinaryMachine.run,clear_symbol,Option.bind_some,ih]
def steps (n : ℕ) : ℕ := (Code.width b b.core.k₀+2)*n+3
theorem prepare (word : List (b.core.Γ b.core.k₀)) (log : List Bool) :
    (machine b).run (steps b word.length)
      (log,initList (computer b) (Code.word b b.core.k₀ word)) =
        some (log,readyCfg b (Compiler.cfg b (initList b.core word))) := by
  have hi : initList (computer b) (Code.word b b.core.k₀ word) =
      scanCfg b (Code.word b b.core.k₀ word) [] [] := by
    change (⟨_,_,_⟩ : (machine b).Config) = ⟨_,_,_⟩
    congr 1
    funext k
    cases k with
    | inl u => cases u; simp [computer,scanCfg,initList,tapes,raw]
    | inr k => cases k with
      | inl _ => simp [computer,scanCfg,initList,tapes,raw]
      | inr k => cases k <;> simp [computer,scanCfg,initList,tapes,raw]
  have hs := scan_run b word [] [] log
  have hm := move_run b (Code.word b b.core.k₀ word).reverse (List.replicate word.length true) [] log
  have hc := clear_run b (List.replicate word.length true) (Code.word b b.core.k₀ word) log
  simp only [List.append_nil] at hs
  simp only [List.append_nil,List.reverse_reverse] at hm
  simp only [List.length_replicate] at hc
  have hf : (machine b).run (steps b word.length)
      (log,initList (computer b) (Code.word b b.core.k₀ word)) =
        some (log,readyCfg b (initList (Compiler.computer b) (Code.word b b.core.k₀ word))) := by
    rw [hi,show steps b word.length =
      (word.length+1)+(((Code.word b b.core.k₀ word).reverse.length+1)+(word.length+1)) by
        simp only [steps,List.length_reverse,Code.word_length,Nat.add_mul]; omega]
    rw [BinaryMachine.run_add,BinaryMachine.run_add,hs,Option.bind_some,hm,Option.bind_some,hc]
  simpa only [Compiler.cfg_init] using hf

def timePolynomial : Polynomial ℕ := Polynomial.C (Code.width b b.core.k₀+2)*Polynomial.X+Polynomial.C 3
theorem steps_le_bits (word : List (b.core.Γ b.core.k₀)) :
    steps b word.length ≤ (timePolynomial b).eval (Code.word b b.core.k₀ word).length := by
  have hw : 1 ≤ Code.width b b.core.k₀ := Code.width_pos b b.core.k₀
  have hn : word.length ≤ Code.width b b.core.k₀*word.length := by
    simpa using Nat.mul_le_mul_right word.length hw
  simpa [steps,timePolynomial,Code.word_length] using Nat.add_le_add_right
    (Nat.mul_le_mul_left (Code.width b b.core.k₀+2) hn) 3
def capacityPolynomial : Polynomial ℕ := Polynomial.X+timePolynomial b*Polynomial.C (machine b).pushBudget
def primitivePolynomial : Polynomial ℕ := timePolynomial b*Polynomial.C (machine b).primitiveBudget
def bitsPolynomial : Polynomial ℕ := Polynomial.C (machine b).controlBits+
  capacityPolynomial b*Polynomial.C (machine b).symbolWidths
def internalBitsPolynomial : Polynomial ℕ := Polynomial.C (machine b).controlBits+
  (capacityPolynomial b+Polynomial.C (machine b).primitiveBudget)*Polynomial.C (machine b).symbolWidths
theorem prefix_capacity (input log : List Bool) (j : ℕ) (next : List Bool × (machine b).Config)
    (hj : j ≤ (timePolynomial b).eval input.length)
    (hr : (machine b).run j (log,initList (computer b) input) = some next) :
    ∀ k, (next.2.stk k).length ≤ (capacityPolynomial b).eval input.length := by
  have hi : ∀ k, ((initList (computer b) input).stk k).length ≤ input.length := by
    intro k; by_cases hk : k = (computer b).k₀ <;> simp [initList,hk]
  have hc := (machine b).run_stack_bound j _ _ input.length hi hr
  intro k
  exact (hc k).trans (by simpa [capacityPolynomial] using
    (Nat.add_le_add_left (Nat.mul_le_mul_right (machine b).pushBudget hj) input.length))
theorem prefix_primitive (input log : List Bool) (j : ℕ) (hj : j ≤ (timePolynomial b).eval input.length) :
    (machine b).primitiveCost j (log,initList (computer b) input) ≤ (primitivePolynomial b).eval input.length :=
  ((machine b).primitiveCost_le j (log,initList (computer b) input)).trans (by simpa [primitivePolynomial] using (Nat.mul_le_mul_right (machine b).primitiveBudget hj))
theorem prefix_bits (input log : List Bool) (j : ℕ) (next : List Bool × (machine b).Config)
    (hj : j ≤ (timePolynomial b).eval input.length)
    (hr : (machine b).run j (log,initList (computer b) input) = some next) :
    (machine b).codedStorageBits next.2 ≤ (bitsPolynomial b).eval input.length :=
  ((machine b).codedStorageBits_le _).trans (by simpa [bitsPolynomial] using ((machine b).storageBits_le next.2 _ (prefix_capacity b input log j next hj hr)))

/-- Reuse the delivered literal opcode-prefix relation and cost producer;
there is no additional executor or supplied temporary-space bound. -/
theorem internal_prefix (input log : List Bool) (j : ℕ) (next : List Bool × (machine b).Config)
    (hj : j < (timePolynomial b).eval input.length)
    (hr : (machine b).run j (log,initList (computer b) input) = some next)
    (l : Label b) (hl : next.2.l = some l) (alternate : Bool) (n : ℕ)
    (v : State b) (S : Stack b → List Bool)
    (hp : NativeExecution.PrimitivePrefix (program b alternate l) next.2.var next.2.stk n v S)
    (control : Option (Label b)) :
    (machine b).primitiveCost j (log,initList (computer b) input)+(n+1) ≤
      (primitivePolynomial b).eval input.length ∧
    (machine b).codedStorageBits ⟨control,v,S⟩ ≤ (internalBitsPolynomial b).eval input.length := by
  have hc := NativeExecution.primitive_prefix_cost _ _ _ _ _ _ hp
  have hn : n+1 ≤ (machine b).primitiveBudget := by
    cases alternate with
    | false => exact (Nat.add_le_add_right hc 1).trans ((machine b).core_budget_le l)
    | true => exact (Nat.add_le_add_right hc 1).trans ((machine b).alternate_budget_le l)
  constructor
  · have he := Nat.add_le_add ((machine b).primitiveCost_le j (log,initList (computer b) input)) hn
    have ht := Nat.mul_le_mul_right (machine b).primitiveBudget (Nat.succ_le_of_lt hj)
    simp only [Nat.succ_mul] at ht
    exact he.trans (by simpa [primitivePolynomial] using ht)
  · have hs := prefix_capacity b input log j next (Nat.le_of_lt hj) hr
    have hu := NativeExecution.primitive_prefix_capacity _ _ _ _ _ _ hp _ hs
    have hb : ∀ k, (S k).length ≤ (capacityPolynomial b).eval input.length+(machine b).primitiveBudget := by
      intro k
      exact (hu k).trans (Nat.add_le_add_left ((Nat.le_add_right n 1).trans hn) _)
    exact ((machine b).codedStorageBits_le _).trans (by
      simpa [internalBitsPolynomial] using (machine b).storageBits_le ⟨control,v,S⟩ _ hb)
end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.GeneralAlphabetInput.Program
