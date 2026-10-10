import Holant.Proofs.CountingMachines.StandardMachine.Support.GeneralAlphabetSharpWitnessCore
import Holant.Proofs.CountingMachines.StandardMachine.Support.BooleanInputWitness.Guard

set_option backward.isDefEq.respectTransparency false
/-! Locally checked adaptation of the frozen reference proof. Total received-word frontend for the ORIGINAL fixed
Γ⊕Bool code. Only left-tagged original symbols are input symbols. The actual
finite reader rejects partial, invalid and right-tagged blocks, erases both
raw and temporary tapes, and returns a clean optional canonical code word.
The host decoder below is a specification, never a statement or callback.
The existing physical packet verifier and unique false padding are reused. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.GeneralAlphabetTotalInput
open Turing Computability Holant.Complexity BinaryCompose FixedFieldMachines
open GraphPreprocessing BooleanOpcode Reverse.Staging StackProtocol
variable (m : BinaryMachine) (T : Polynomial ℕ) (acceptControl : m.core.σ → Bool)
local instance : Fintype (m.core.Γ m.core.k₀) := m.alphabets m.core.k₀

abbrev Γ := m.core.Γ m.core.k₀
def originalWitness := GeneralAlphabetSharpWitness.source m T acceptControl (encodingList (Γ m))
def codeWord (word : List (Γ m)) : List Bool :=
  GeneralAlphabetInput.raw m T acceptControl word []

@[simp] theorem input_code (word : List (Γ m)) :
    (BooleanInputWitness.inputEncoding (originalWitness m T acceptControl)).encode word =
      codeWord m T acceptControl word := by
  simp [BooleanInputWitness.inputEncoding,BooleanInputWitness.pairEncoding,
    BooleanInputWitness.payload,originalWitness,GeneralAlphabetSharpWitness.source,
    Program.verifier,encodingProd,encodingList,codeWord,GeneralAlphabetInput.raw,
    GeneralAlphabetInput.rawCode,GeneralAlphabetInput.taggedWord,GeneralAlphabetInput.s,
    BooleanInputWitness.original,Program.deterministic,Function.comp_def]
  rfl

namespace Parser
/-- Metadata inherits the exact OLD input Fintype, not a new enumeration. -/
abbrev table : BinaryMachine where
  core := {
    K := Fin 3
    k₀ := 0
    k₁ := 2
    Γ k := if k=0 then GeneralAlphabetInput.TaggedSymbol m else Bool
    Γk₀Fin := by
      change Fintype (GeneralAlphabetInput.TaggedSymbol m)
      exact (GeneralAlphabetInput.s m T acceptControl).alphabets
        (GeneralAlphabetInput.s m T acceptControl).core.k₀
    Λ := Fin 4
    main := 0
    σ := Unit
    initialState := ()
    m _ := .halt }
  alternate _ := .halt
  split _ := false
  alphabets k := by
    change Fintype (if k=0 then GeneralAlphabetInput.TaggedSymbol m else Bool)
    by_cases hk : k = 0
    · subst k
      change Fintype (GeneralAlphabetInput.TaggedSymbol m)
      exact (GeneralAlphabetInput.s m T acceptControl).alphabets
        (GeneralAlphabetInput.s m T acceptControl).core.k₀
    · simpa only [hk,ite_false] using inferInstanceAs (Fintype Bool)

abbrev State := Block.State (table m T acceptControl)
def initial : State m T acceptControl := Block.clear (table m T acceptControl) ()
def width : ℕ := Code.width (table m T acceptControl) 0
def symbol (a : Γ m) : List Bool := Code.symbol (table m T acceptControl) 0 (Sum.inl a)

theorem width_eq : width m T acceptControl = GeneralAlphabetInput.rawWidth m T acceptControl := rfl
theorem symbol_eq (a : Γ m) : symbol m T acceptControl a =
    GeneralAlphabetInput.rawSymbol m T acceptControl (Sum.inl a) := rfl
@[simp] theorem width_pos : 0 < width m T acceptControl := Code.width_pos _ _
@[simp] theorem symbol_length (a : Γ m) : (symbol m T acceptControl a).length = width m T acceptControl :=
  Code.symbol_length _ _ _
@[simp] theorem code_nil : codeWord m T acceptControl [] = [] := rfl
@[simp] theorem code_cons (a : Γ m) (word : List (Γ m)) :
    codeWord m T acceptControl (a::word) = symbol m T acceptControl a++codeWord m T acceptControl word := rfl
@[simp] theorem code_length (word : List (Γ m)) :
    (codeWord m T acceptControl word).length = width m T acceptControl*word.length := by
  simpa only [codeWord,width_eq,List.length_nil,Nat.add_zero] using
    GeneralAlphabetInput.raw_length m T acceptControl word []

/-- Bounded mathematical grammar specification, not a runtime decoder. -/
def parseFuel : ℕ → List Bool → Option (List (Γ m))
  | 0,bits => if bits=[] then some [] else none
  | n+1,bits => if bits=[] then some [] else
      (Code.decode (table m T acceptControl) 0 (bits.take (width m T acceptControl))).bind
        (fun tag => match tag with
          | .inl a => (parseFuel n (bits.drop (width m T acceptControl))).map (a::·)
          | .inr _ => none)
def parse (bits : List Bool) := parseFuel m T acceptControl bits.length bits

theorem parseFuel_sound (n : ℕ) (bits : List Bool) (word : List (Γ m))
    (h : parseFuel m T acceptControl n bits = some word) : codeWord m T acceptControl word = bits := by
  induction n generalizing bits word with
  | zero =>
      by_cases hb : bits=[]
      · subst bits; simp [parseFuel] at h; subst word; rfl
      · simp [parseFuel,hb] at h
  | succ n ih =>
      by_cases hb : bits=[]
      · subst bits; simp [parseFuel] at h; subst word; rfl
      · cases hd : Code.decode (table m T acceptControl) 0 (bits.take (width m T acceptControl)) with
        | none => simp [parseFuel,hb,hd] at h
        | some tag =>
            cases tag with
            | inr b => simp [parseFuel,hb,hd] at h
            | inl a =>
                cases hr : parseFuel m T acceptControl n (bits.drop (width m T acceptControl)) with
                | none => simp [parseFuel,hb,hd,hr] at h
                | some rest =>
                    have hw : a::rest=word := by simpa [parseFuel,hb,hd,hr] using h
                    subst word
                    rw [code_cons,ih _ _ hr]
                    exact (congrArg (·++bits.drop (width m T acceptControl))
                      (Code.decode_sound _ _ _ _ hd)).trans (List.take_append_drop _ _)

theorem parseFuel_code (word : List (Γ m)) (n : ℕ) (hn : word.length ≤ n) :
    parseFuel m T acceptControl n (codeWord m T acceptControl word) = some word := by
  induction word generalizing n with
  | nil => cases n <;> simp [parseFuel]
  | cons a word ih =>
      cases n with
      | zero => simp only [List.length_cons] at hn; omega
      | succ n =>
          have hne : codeWord m T acceptControl (a::word) ≠ [] := by
            intro he
            have hl := congrArg List.length he
            simp only [code_length,List.length_cons,List.length_nil] at hl
            exact (Nat.ne_of_gt (Nat.mul_pos (width_pos m T acceptControl) (Nat.succ_pos _))) hl
          have ht : (codeWord m T acceptControl (a::word)).take (width m T acceptControl)=
              symbol m T acceptControl a := by
            simp [code_cons,symbol,width,List.take_append,Code.symbol_length]
          have hd : (codeWord m T acceptControl (a::word)).drop (width m T acceptControl)=
              codeWord m T acceptControl word := by
            simp [code_cons,symbol,width,List.drop_append,Code.symbol_length]
          rw [parseFuel,if_neg hne,ht,hd]
          change (Code.decode (table m T acceptControl) 0
            (Code.symbol (table m T acceptControl) 0 (Sum.inl a))).bind _=some (a::word)
          rw [Code.decode_symbol,Option.bind_some,
            ih n (by simpa only [List.length_cons,Nat.succ_le_succ_iff] using hn)] <;> rfl

@[simp] theorem parse_code (word : List (Γ m)) : parse m T acceptControl (codeWord m T acceptControl word) = some word := by
  apply parseFuel_code
  rw [code_length]
  simpa only [Nat.one_mul] using Nat.mul_le_mul_right word.length (Nat.succ_le_of_lt (width_pos m T acceptControl))

theorem parse_sound (bits : List Bool) (word : List (Γ m))
    (h : parse m T acceptControl bits = some word) : codeWord m T acceptControl word = bits :=
  parseFuel_sound m T acceptControl _ _ _ h

theorem parse_image (bits : List Bool) :
    (parse m T acceptControl bits).isSome = true ↔ ∃ word, codeWord m T acceptControl word=bits := by
  cases h : parse m T acceptControl bits with
  | none =>
      simp only [Option.isSome_none,Bool.false_eq_true,false_iff]
      rintro ⟨word,hw⟩
      have hp := parse_code m T acceptControl word
      rw [hw,h] at hp
      cases hp
  | some word => simp only [Option.isSome_some,true_iff]; exact ⟨word,parse_sound m T acceptControl bits word h⟩

def states : StateEmbedding (State m T acceptControl) (State m T acceptControl) := ⟨id,id,fun _ => rfl⟩
def leaf (head : Option (GeneralAlphabetInput.TaggedSymbol m)) :
    TM2.Stmt (fun _ : Fin 3 => Bool) (Fin 4) (State m T acceptControl) :=
  match head with
  | none => .goto (fun _ => 1)
  | some (.inr _) => .goto (fun _ => 2)
  | some (.inl a) => Block.pushVector (table m T acceptControl) 1 (width m T acceptControl)
      (fun i _ => Code.bit (table m T acceptControl) 0 (Sum.inl a) i.rev)
      (.load (fun _ => initial m T acceptControl) (.goto (fun _ => 0)))
def read := HeterogeneousSum.restateStmt (fun _ : Fin 3 => Bool)
  (states m T acceptControl) id (some 2)
  (Block.readSymbol (table m T acceptControl) 0 (leaf m T acceptControl))
def program (l : Fin 4) : TM2.Stmt (fun _ : Fin 3 => Bool) (Fin 4) (State m T acceptControl) :=
  if l=0 then read m T acceptControl
  else if l=1 then .pop 1 (Block.setBit (table m T acceptControl))
    (.branch (fun v => v.2.1.isSome)
      (.push 2 (fun v => v.2.1.getD false)
        (.load (fun _ => initial m T acceptControl) (.goto (fun _ => 1))))
      (.push 2 (fun _ => true) (.load (fun _ => initial m T acceptControl) .halt)))
  else if l=2 then .pop 0 (Block.setBit (table m T acceptControl))
    (.branch (fun v => v.2.1.isSome)
      (.load (fun _ => initial m T acceptControl) (.goto (fun _ => 2)))
      (.load (fun _ => initial m T acceptControl) (.goto (fun _ => 3))))
  else .pop 1 (Block.setBit (table m T acceptControl))
    (.branch (fun v => v.2.1.isSome)
      (.load (fun _ => initial m T acceptControl) (.goto (fun _ => 3)))
      (.push 2 (fun _ => false) (.load (fun _ => initial m T acceptControl) .halt)))
def machine : Machine where
  K := Fin 3
  input := 0
  output := 2
  Label := Fin 4
  main := 0
  State := State m T acceptControl
  initial := initial m T acceptControl
  program := program m T acceptControl
def tapes (raw temporary output : List Bool) : Fin 3 → List Bool := ![raw,temporary,output]
@[simp] theorem tapes_zero (raw temporary output : List Bool) : tapes raw temporary output 0 = raw := rfl
@[simp] theorem tapes_one (raw temporary output : List Bool) : tapes raw temporary output 1 = temporary := rfl
@[simp] theorem tapes_two (raw temporary output : List Bool) : tapes raw temporary output 2 = output := rfl

def row (l : Fin 4) (v : State m T acceptControl) (raw temporary output : List Bool) : (machine m T acceptControl).Config :=
  ⟨some l,v,tapes raw temporary output⟩
def scan (raw temporary : List Bool) := row m T acceptControl 0 (initial m T acceptControl) raw temporary []

theorem update (k : Fin 3) (raw temporary output word : List Bool) :
    Function.update (tapes raw temporary output) k word =
      tapes (if k=0 then word else raw) (if k=1 then word else temporary) (if k=2 then word else output) := by
  funext j; fin_cases k <;> fin_cases j <;> rfl
@[simp] theorem initial_eq (bits : List Bool) :
    initList (machine m T acceptControl).computer bits = scan m T acceptControl bits [] := by
  rw [Machine.init_eq]
  congr 1; funext k; fin_cases k <;> rfl
@[simp] theorem terminal_eq (bits : List Bool) :
    haltList (machine m T acceptControl).computer bits =
      ⟨none,initial m T acceptControl,tapes [] [] bits⟩ := by
  rw [Machine.halt_eq]
  congr 1; funext k; fin_cases k <;> rfl

theorem reversed_symbol (a : Γ m) :
    List.ofFn (fun i : Fin (width m T acceptControl) => Code.bit (table m T acceptControl) 0 (Sum.inl a) i.rev) =
      (symbol m T acceptControl a).reverse := by
  apply List.ext_getElem
  · simp only [symbol,Code.symbol,List.length_ofFn,List.length_reverse,width]
  · intro i hi hj
    simp only [symbol,Code.symbol,List.getElem_ofFn,List.getElem_reverse,List.length_ofFn]
    apply congrArg (Code.bit (table m T acceptControl) 0 (Sum.inl a))
    apply Fin.ext
    simp only [Fin.rev]
    change width m T acceptControl - (i+1) = Code.width (table m T acceptControl) 0 - 1 - i
    unfold width
    omega

theorem read_eval (v : State m T acceptControl) (S : Fin 3 → List Bool) :
    TM2.stepAux (read m T acceptControl) v S =
      HeterogeneousSum.restateCfg (fun _ : Fin 3 => Bool) (states m T acceptControl) id (some 2)
        (TM2.stepAux (Block.readSymbol (table m T acceptControl) 0 (leaf m T acceptControl)) v S) := by
  exact HeterogeneousSum.restate_stepAux (fun _ : Fin 3 => Bool)
    (states m T acceptControl) id (some 2) _ v S

theorem read_symbol (tag : GeneralAlphabetInput.TaggedSymbol m) (rest temporary : List Bool) :
    (machine m T acceptControl).computer.step
      (scan m T acceptControl (Code.symbol (table m T acceptControl) 0 tag++rest) temporary) =
      some (match tag with
        | .inl a => scan m T acceptControl rest ((symbol m T acceptControl a).reverse++temporary)
        | .inr _ => row m T acceptControl 2 (initial m T acceptControl) rest temporary []) := by
  have hu : tapes (Code.symbol (table m T acceptControl) 0 tag++rest) temporary [] =
      Function.update (tapes rest temporary []) 0 (Code.symbol (table m T acceptControl) 0 tag++rest) := by
    rw [update] <;> rfl
  change some (TM2.stepAux (read m T acceptControl) (initial m T acceptControl)
    (tapes (Code.symbol (table m T acceptControl) 0 tag++rest) temporary [])) = _
  have hr := Block.read_symbol (table m T acceptControl) 0 (leaf m T acceptControl)
    tag (initial m T acceptControl) (tapes rest temporary [])
  simp only [tapes_zero] at hr
  rw [read_eval,hu,hr]
  cases tag with
  | inl a =>
      rw [leaf,Block.pushVector_eval,reversed_symbol,update]
      simp [TM2.stepAux,HeterogeneousSum.restateCfg,states,initial,scan,row]
  | inr bit => simp [leaf,TM2.stepAux,HeterogeneousSum.restateCfg,states,initial,row]

theorem read_empty (temporary : List Bool) :
    (machine m T acceptControl).computer.step (scan m T acceptControl [] temporary) =
      some (row m T acceptControl 1 (initial m T acceptControl) [] temporary []) := by
  change some (TM2.stepAux (read m T acceptControl) (initial m T acceptControl) (tapes [] temporary [])) = _
  rw [read_eval,Block.read_empty _ _ _ _ _ (show tapes [] temporary [] 0=[] from rfl)]
  simp [leaf,TM2.stepAux,HeterogeneousSum.restateCfg,states,initial,row]

/-- Complete bad-block semantics for the EXISTING unrolled reader. -/
theorem read_bad_exact (n : ℕ) (pre bits : List Bool) (hlen : bits.length=n)
    (hd : Code.decode (table m T acceptControl) 0 (pre++bits)=none)
    (v : State m T acceptControl) (S : Fin 3 → List Bool) :
    TM2.stepAux (Block.read (table m T acceptControl) 0 (leaf m T acceptControl) n pre) v
      (Function.update S 0 (bits++S 0)) = TM2.stepAux (Block.bad (table m T acceptControl)) v S := by
  induction n generalizing pre bits v S with
  | zero =>
      have hb : bits=[] := List.length_eq_zero_iff.mp hlen
      subst bits
      simp only [List.append_nil] at hd
      simp [Block.read,hd,TM2.stepAux,Function.update_eq_self]
  | succ n ih =>
      cases bits with
      | nil => simp at hlen
      | cons b bits =>
          have hn : bits.length=n := by simpa only [List.length_cons,Nat.succ.injEq] using hlen
          cases b with
          | false =>
              simpa [Block.read,TM2.stepAux,Block.setBit,Block.bad,
                List.append_assoc,Function.update_idem] using
                (ih (pre++[false]) bits hn (by simpa only [List.append_assoc,List.singleton_append] using hd)
                  (Block.setBit (table m T acceptControl) v (some false)) S)
          | true =>
              simpa [Block.read,TM2.stepAux,Block.setBit,Block.bad,
                List.append_assoc,Function.update_idem] using
                (ih (pre++[true]) bits hn (by simpa only [List.append_assoc,List.singleton_append] using hd)
                  (Block.setBit (table m T acceptControl) v (some true)) S)

theorem read_bad_partial (n : ℕ) (pre bits : List Bool) (hlen : bits.length<n)
    (hne : pre≠[] ∨ bits≠[]) (v : State m T acceptControl)
    (S : Fin 3 → List Bool) (hS : S 0=[]) :
    TM2.stepAux (Block.read (table m T acceptControl) 0 (leaf m T acceptControl) n pre) v
      (Function.update S 0 bits) = TM2.stepAux (Block.bad (table m T acceptControl)) v S := by
  induction n generalizing pre bits v with
  | zero => omega
  | succ n ih =>
      cases bits with
      | nil =>
          have hp : pre≠[] := hne.resolve_right (by simp)
          have hu : Function.update S 0 []=S := by simpa only [hS] using Function.update_eq_self 0 S
          simp [Block.read,TM2.stepAux,Block.setBit,Block.bad,hp,hu,hS]
      | cons b bits =>
          have hn : bits.length<n := by simpa only [List.length_cons,Nat.succ_lt_succ_iff] using hlen
          cases b with
          | false =>
              simpa [Block.read,TM2.stepAux,Block.setBit,Block.bad,Function.update_idem] using
                (ih (pre++[false]) bits hn (Or.inl (by simp))
                  (Block.setBit (table m T acceptControl) v (some false)))
          | true =>
              simpa [Block.read,TM2.stepAux,Block.setBit,Block.bad,Function.update_idem] using
                (ih (pre++[true]) bits hn (Or.inl (by simp))
                  (Block.setBit (table m T acceptControl) v (some true)))

theorem bad_full (bits rest temporary : List Bool) (hlen : bits.length=width m T acceptControl)
    (hd : Code.decode (table m T acceptControl) 0 bits=none) :
    (machine m T acceptControl).computer.step (scan m T acceptControl (bits++rest) temporary) =
      some (row m T acceptControl 2 ((),none,false) rest temporary []) := by
  change some (TM2.stepAux (read m T acceptControl) (initial m T acceptControl) (tapes (bits++rest) temporary [])) = _
  have hu : tapes (bits++rest) temporary []=Function.update (tapes rest temporary []) 0 (bits++rest) := by rw [update] <;> rfl
  have hr := read_bad_exact m T acceptControl (Code.width (table m T acceptControl) 0) [] bits
    hlen (by simpa only [List.nil_append] using hd) (initial m T acceptControl) (tapes rest temporary [])
  simp only [tapes_zero] at hr
  rw [read_eval,hu,Block.readSymbol,hr]
  simp [Block.bad,TM2.stepAux,HeterogeneousSum.restateCfg,states,row,initial]

theorem bad_partial (bits temporary : List Bool) (hne : bits≠[]) (hlen : bits.length<width m T acceptControl) :
    (machine m T acceptControl).computer.step (scan m T acceptControl bits temporary) =
      some (row m T acceptControl 2 ((),none,false) [] temporary []) := by
  change some (TM2.stepAux (read m T acceptControl) (initial m T acceptControl) (tapes bits temporary [])) = _
  have hu : tapes bits temporary []=Function.update (tapes [] temporary []) 0 bits := by rw [update] <;> rfl
  have hr := read_bad_partial m T acceptControl (Code.width (table m T acceptControl) 0) [] bits
    hlen (Or.inr hne) (initial m T acceptControl) (tapes [] temporary []) rfl
  simp only [tapes_zero] at hr
  rw [read_eval,hu,Block.readSymbol,hr]
  simp [Block.bad,TM2.stepAux,HeterogeneousSum.restateCfg,states,row,initial]

/-- Exact iteration for this parser's finite control and register state. -/
def RunsExactly {α : Type} (step : α → Option α) (a b : α) (steps : ℕ) : Prop :=
  (fun c => c.bind step)^[steps] (some a) = some b

theorem runsExactly_one {α : Type} {step : α → Option α} {a b : α}
    (h : step a = some b) : RunsExactly step a b 1 := h

theorem RunsExactly.trans {α : Type} {step : α → Option α} {a b c : α} {n k : ℕ}
    (h : RunsExactly step a b n) (h' : RunsExactly step b c k) :
    RunsExactly step a c (k+n) := by
  unfold RunsExactly at *
  rw [Function.iterate_add_apply,h,h']

theorem move_run (temporary output : List Bool) :
    RunsExactly (machine m T acceptControl).computer.step
      (row m T acceptControl 1 (initial m T acceptControl) [] temporary output)
      (haltList (machine m T acceptControl).computer (true::(temporary.reverse++output))) (temporary.length+1) := by
  induction temporary generalizing output with
  | nil => apply runsExactly_one; rw [terminal_eq]; simp [FinTM2.step,TM2.step,machine,program,row,TM2.stepAux,initial,Block.setBit,terminal_eq,update]
  | cons bit temporary ih =>
      have hs : (machine m T acceptControl).computer.step
          (row m T acceptControl 1 (initial m T acceptControl) [] (bit::temporary) output) =
          some (row m T acceptControl 1 (initial m T acceptControl) [] temporary (bit::output)) := by
        simp [FinTM2.step,TM2.step,machine,program,row,TM2.stepAux,initial,Block.setBit,update]
      simpa [List.reverse_cons,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
        (runsExactly_one hs).trans (ih (bit::output))

theorem clear_temporary (v : State m T acceptControl) (temporary : List Bool) :
    RunsExactly (machine m T acceptControl).computer.step
      (row m T acceptControl 3 v [] temporary [])
      (haltList (machine m T acceptControl).computer [false]) (temporary.length+1) := by
  induction temporary generalizing v with
  | nil => apply runsExactly_one; rw [terminal_eq]; simp [FinTM2.step,TM2.step,machine,program,row,TM2.stepAux,initial,Block.setBit,terminal_eq,update]
  | cons bit temporary ih =>
      have hs : (machine m T acceptControl).computer.step (row m T acceptControl 3 v [] (bit::temporary) []) =
          some (row m T acceptControl 3 (initial m T acceptControl) [] temporary []) := by
        simp [FinTM2.step,TM2.step,machine,program,row,TM2.stepAux,initial,Block.setBit,update]
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using (runsExactly_one hs).trans (ih (initial m T acceptControl))

theorem reject_run (v : State m T acceptControl) (bits temporary : List Bool) :
    RunsExactly (machine m T acceptControl).computer.step
      (row m T acceptControl 2 v bits temporary [])
      (haltList (machine m T acceptControl).computer [false]) (bits.length+temporary.length+2) := by
  induction bits generalizing v with
  | nil =>
      have hs : (machine m T acceptControl).computer.step (row m T acceptControl 2 v [] temporary []) =
          some (row m T acceptControl 3 (initial m T acceptControl) [] temporary []) := by
        simp [FinTM2.step,TM2.step,machine,program,row,TM2.stepAux,initial,Block.setBit,update]
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using (runsExactly_one hs).trans
        (clear_temporary m T acceptControl (initial m T acceptControl) temporary)
  | cons bit bits ih =>
      have hs : (machine m T acceptControl).computer.step (row m T acceptControl 2 v (bit::bits) temporary []) =
          some (row m T acceptControl 2 (initial m T acceptControl) bits temporary []) := by
        simp [FinTM2.step,TM2.step,machine,program,row,TM2.stepAux,initial,Block.setBit,update]
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using (runsExactly_one hs).trans (ih (initial m T acceptControl))

def result (temporary : List Bool) (parsed : Option (List (Γ m))) : List Bool :=
  parsed.elim [false] (fun word => true::(temporary.reverse++codeWord m T acceptControl word))

/-- ALL received words, with no decoding-success or trajectory premise. -/
theorem run_all (n : ℕ) (bits temporary : List Bool) (hn : bits.length≤n) :
    ∃ steps, steps≤n+bits.length+temporary.length+2 ∧
      RunsExactly (machine m T acceptControl).computer.step (scan m T acceptControl bits temporary)
        (haltList (machine m T acceptControl).computer
          (result m T acceptControl temporary (parseFuel m T acceptControl n bits))) steps := by
  induction n generalizing bits temporary with
  | zero =>
      have hb : bits=[] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hn)
      subst bits
      refine ⟨temporary.length+2,by simp,?_⟩
      simpa [parseFuel,result,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
        (runsExactly_one (read_empty m T acceptControl temporary)).trans (move_run m T acceptControl temporary [])
  | succ n ih =>
      by_cases hb : bits=[]
      · subst bits
        refine ⟨temporary.length+2,by simp <;> omega,?_⟩
        simpa [parseFuel,result,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
          (runsExactly_one (read_empty m T acceptControl temporary)).trans (move_run m T acceptControl temporary [])
      · by_cases hw : width m T acceptControl≤bits.length
        · have ht : (bits.take (width m T acceptControl)).length=width m T acceptControl :=
            by simp only [List.length_take,Nat.min_eq_left hw]
          have he := List.take_append_drop (width m T acceptControl) bits
          have hl : bits.length=width m T acceptControl+(bits.drop (width m T acceptControl)).length := by
            have h := congrArg List.length he
            simpa only [List.length_append,ht] using h.symm
          cases hd : Code.decode (table m T acceptControl) 0 (bits.take (width m T acceptControl)) with
          | none =>
              have hs := bad_full m T acceptControl (bits.take (width m T acceptControl)) (bits.drop (width m T acceptControl)) temporary ht hd
              rw [he] at hs
              refine ⟨(bits.drop (width m T acceptControl)).length+temporary.length+3,by omega,?_⟩
              convert (runsExactly_one hs).trans (reject_run m T acceptControl ((),none,false) _ temporary) using 1 <;>
                (try rfl) <;> (try simp [parseFuel,hb,hd,result]) <;> omega
          | some tag =>
              have hc := Code.decode_sound (table m T acceptControl) 0 _ tag hd
              have hword : Code.symbol (table m T acceptControl) 0 tag++bits.drop (width m T acceptControl)=bits := by rw [hc]; exact he
              have hs := read_symbol m T acceptControl tag (bits.drop (width m T acceptControl)) temporary
              rw [hword] at hs
              cases tag with
              | inr bit =>
                  refine ⟨(bits.drop (width m T acceptControl)).length+temporary.length+3,by omega,?_⟩
                  convert (runsExactly_one hs).trans (reject_run m T acceptControl (initial m T acceptControl) _ temporary) using 1 <;>
                    (try rfl) <;> (try simp [parseFuel,hb,hd,result]) <;> omega
              | inl a =>
                  have hrn : (bits.drop (width m T acceptControl)).length≤n := by have hp := width_pos m T acceptControl; omega
                  obtain ⟨steps,hle,hr⟩ := ih (bits.drop (width m T acceptControl))
                    ((symbol m T acceptControl a).reverse++temporary) hrn
                  refine ⟨steps+1,?_,?_⟩
                  · simp only [List.length_append,List.length_reverse,symbol_length] at hle; omega
                  · cases hp : parseFuel m T acceptControl n (bits.drop (width m T acceptControl)) <;>
                      simpa [parseFuel,hb,hd,result,hp,code_cons,List.reverse_append,
                        List.reverse_reverse,List.append_assoc,Nat.add_comm] using
                        (runsExactly_one hs).trans hr
        · have hshort : bits.length<width m T acceptControl := Nat.lt_of_not_ge hw
          have hd : Code.decode (table m T acceptControl) 0 (bits.take (width m T acceptControl))=none := by
            cases h : Code.decode (table m T acceptControl) 0 (bits.take (width m T acceptControl)) with
            | none => rfl
            | some tag =>
                have hc := congrArg List.length (Code.decode_sound _ _ _ _ h)
                simp only [Code.symbol_length,List.length_take] at hc
                change width m T acceptControl = min (width m T acceptControl) bits.length at hc
                omega
          refine ⟨temporary.length+3,by omega,?_⟩
          simpa [parseFuel,hb,hd,result,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
            (runsExactly_one (bad_partial m T acceptControl bits temporary hb hshort)).trans
              (reject_run m T acceptControl ((),none,false) [] temporary)

def computes : Computes Frame.wordEncoding BooleanInputWitness.Guard.outputEncoding
    (fun bits => (parse m T acceptControl bits).map (codeWord m T acceptControl)) where
  machine := machine m T acceptControl
  time := 2*Polynomial.X+2
  outputs bits := by
    let witness := run_all m T acceptControl bits.length bits [] (Nat.le_refl _)
    let steps := witness.choose
    have hle := witness.choose_spec.1
    have hr := witness.choose_spec.2
    change RunsExactly (machine m T acceptControl).computer.step (scan m T acceptControl bits [])
      (haltList (machine m T acceptControl).computer
        (result m T acceptControl [] (parseFuel m T acceptControl bits.length bits))) steps at hr
    change steps ≤ bits.length+bits.length+[].length+2 at hle
    refine { steps := steps, evals_in_steps := ?_, steps_le_m := ?_ }
    · change RunsExactly (machine m T acceptControl).computer.step
        (initList (machine m T acceptControl).computer bits)
        (haltList (machine m T acceptControl).computer
          (BooleanInputWitness.Guard.outputEncoding.encode
            ((parse m T acceptControl bits).map (codeWord m T acceptControl)))) steps
      cases h : parseFuel m T acceptControl bits.length bits <;>
        simpa only [initial_eq,parse,result,h,Option.map_none,Option.map_some,Option.elim_none,
          Option.elim_some,BooleanInputWitness.Guard.outputEncoding,List.reverse_nil,List.nil_append,
          Frame.wordEncoding] using hr
    · simp only [Frame.wordEncoding,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,
        Polynomial.eval_X]
      change steps ≤ 2*bits.length+2
      change steps ≤ bits.length+bits.length+[].length+2 at hle
      simpa only [List.length_nil,Nat.add_zero,two_mul] using hle

theorem restate_budget (q : TM2.Stmt (fun _ : Fin 3 => Bool) (Fin 4) (State m T acceptControl)) :
    HeterogeneousCost.budget (HeterogeneousSum.restateStmt (fun _ : Fin 3 => Bool)
      (states m T acceptControl) id (some 2) q)=HeterogeneousCost.budget q := by
  induction q <;> simp [HeterogeneousSum.restateStmt,HeterogeneousCost.budget, *]

/-- The scanner's fixed finite tree has a literal primitive bound. The only
loops are source-symbol scan, bit transfer and two erasers. -/
theorem literal_budget (l : Fin 4) :
    HeterogeneousCost.budget ((machine m T acceptControl).program l)≤4*width m T acceptControl+5 := by
  have hl : ∀ head, HeterogeneousCost.budget (leaf m T acceptControl head)≤width m T acceptControl+2 := by
    intro head
    cases head with
    | none => simp [leaf,HeterogeneousCost.budget]
    | some tag =>
        cases tag with
        | inr b => simp [leaf,HeterogeneousCost.budget]
        | inl a =>
            simp only [leaf]
            rw [Block.pushVector_budget (table m T acceptControl)]
            simp [HeterogeneousCost.budget]
  have hr := Block.read_budget (table m T acceptControl) 0 (leaf m T acceptControl)
    (width m T acceptControl+2) hl (width m T acceptControl) []
  have hread : HeterogeneousCost.budget (read m T acceptControl)≤
      3*width m T acceptControl+(width m T acceptControl+2)+3 := by
    simpa only [read,restate_budget,Block.readSymbol,width] using hr
  fin_cases l
  · change HeterogeneousCost.budget (read m T acceptControl)≤4*width m T acceptControl+5
    exact hread.trans (by omega)
  · simp [machine,program,HeterogeneousCost.budget] <;> omega
  · simp [machine,program,HeterogeneousCost.budget] <;> omega
  · simp [machine,program,HeterogeneousCost.budget] <;> omega
end Parser
end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.GeneralAlphabetTotalInput
