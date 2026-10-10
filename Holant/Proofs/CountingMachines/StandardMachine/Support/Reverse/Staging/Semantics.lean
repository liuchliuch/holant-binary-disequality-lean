import Holant.Proofs.CountingMachines.StandardMachine.Support.Reverse.Staging.Program

set_option backward.isDefEq.respectTransparency false
/-! Adapted reference proof. See the task validation reports. The original tagged bytes are read by real pops. Both
field reversals are literal loops. The clock run consumes the existing actual
unary polynomial machine, preserving all original source/packet tapes. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Reverse.Staging.Program
open Turing Holant.Complexity BinaryCompose
open Holant.Complexity.GraphPreprocessing
variable (m : BinaryMachine) (T : Polynomial ℕ) (acceptControl : m.core.σ → Bool)
local instance : Fintype m.core.K := m.core.kFin
local instance : Fintype m.core.Λ := m.core.ΛFin
local instance : Fintype m.core.σ := m.core.σFin
local instance (k : m.core.K) : Fintype (m.core.Γ k) := m.alphabets k
local instance (k : Stack m T) : Fintype (Alphabet m T k) :=
  (deterministic m T (fun _ => false)).alphabets k

def extras (input : List (m.core.Γ m.core.k₀ ⊕ Bool))
    (original : List (m.core.Γ m.core.k₀)) (bits : List Bool) :
    ∀ k, List (ExtraAlphabet m k)
  | .inl _ => input
  | .inr (.inl _) => original
  | .inr (.inr _) => bits

def tapes (prep : (clock T).K → List Bool)
    (input : List (m.core.Γ m.core.k₀ ⊕ Bool))
    (original : List (m.core.Γ m.core.k₀)) (bits packetWord : List Bool)
    (source : ∀ k, List (m.core.Γ k)) : ∀ k, List (Alphabet m T k) :=
  SumStacks.merge (InnerAlphabet m) prep
    (HeterogeneousSum.merge (ExtraAlphabet m) (Reverse.Program.Alphabet m)
      (extras m input original bits)
      (SumStacks.merge m.core.Γ (fun _ : Unit => packetWord) source))

def scratchState (seen : Bool) : State m T := setSeen m T (initial m T) seen

def scanCfg (seen : Bool) (input : List (m.core.Γ m.core.k₀ ⊕ Bool))
    (original : List (m.core.Γ m.core.k₀)) (bits : List Bool) (n : ℕ) :
    (computer m T acceptControl).Cfg :=
  ⟨some (scanner m T 0),scratchState m T seen,
    tapes m T (wordTape (clock T).input (List.replicate n true))
      input original bits [] (fun _ => [])⟩

def originalCfg (seen : Bool) (original : List (m.core.Γ m.core.k₀))
    (bits : List Bool) (n : ℕ) (word : List (m.core.Γ m.core.k₀)) :
    (computer m T acceptControl).Cfg :=
  ⟨some (scanner m T 1),scratchState m T seen,
    tapes m T (wordTape (clock T).input (List.replicate n true))
      [] original bits [] (initList m.core word).stk⟩

def packetCfg (seen : Bool) (bits : List Bool) (n : ℕ)
    (word : List (m.core.Γ m.core.k₀)) (packetWord : List Bool) :
    (computer m T acceptControl).Cfg :=
  ⟨some (scanner m T 2),scratchState m T seen,
    tapes m T (wordTape (clock T).input (List.replicate n true))
      [] [] bits packetWord (initList m.core word).stk⟩

def clockCfg (word : List (m.core.Γ m.core.k₀)) (bits : List Bool)
    (c : (clock T).Config) : (computer m T acceptControl).Cfg :=
  SumStacks.leftCfg (InnerAlphabet m)
    (HeterogeneousSum.merge (ExtraAlphabet m) (Reverse.Program.Alphabet m) (extras m [] [] [])
      (SumStacks.merge m.core.Γ (fun _ : Unit => bits) (initList m.core word).stk))
    (embedCfg (clockLayout T) (clockStates m T) Sum.inl
      (some (interpreter m T (Reverse.Program.label m (some m.core.main) 0))) c)

theorem extras_update_raw (input next : List (m.core.Γ m.core.k₀ ⊕ Bool))
    (original : List (m.core.Γ m.core.k₀)) (bits : List Bool) :
    Function.update (extras m input original bits) (.inl ()) next = extras m next original bits := by
  funext k
  cases k with
  | inl u => cases u; rfl
  | inr k => cases k <;> simp [extras]

theorem extras_update_original (input : List (m.core.Γ m.core.k₀ ⊕ Bool))
    (original next : List (m.core.Γ m.core.k₀)) (bits : List Bool) :
    Function.update (extras m input original bits) (.inr (.inl ())) next =
      extras m input next bits := by
  funext k
  cases k with
  | inl u => simp [extras]
  | inr k => cases k with
    | inl u => cases u; rfl
    | inr u => simp [extras]

theorem extras_update_packet (input : List (m.core.Γ m.core.k₀ ⊕ Bool))
    (original : List (m.core.Γ m.core.k₀)) (bits next : List Bool) :
    Function.update (extras m input original bits) (.inr (.inr ())) next =
      extras m input original next := by
  funext k
  cases k with
  | inl u => simp [extras]
  | inr k => cases k with
    | inl u => simp [extras]
    | inr u => cases u; rfl

theorem initial_raw (input : List (m.core.Γ m.core.k₀ ⊕ Bool)) :
    scanCfg m T acceptControl false input [] [] 0 = initList (computer m T acceptControl) input := by
  simp only [scanCfg,scratchState,setSeen,initial,computer,initList,scanner]
  congr 1
  funext k
  cases k with
  | inl k => simp [tapes,SumStacks.merge,wordTape,raw]
  | inr k =>
    cases k with
    | inl k =>
      cases k with
      | inl u => cases u; simp [tapes,SumStacks.merge,HeterogeneousSum.merge,extras,raw]
      | inr k => cases k <;> simp [tapes,SumStacks.merge,HeterogeneousSum.merge,extras,raw]
    | inr k => cases k <;> simp [tapes,SumStacks.merge,HeterogeneousSum.merge,raw]

theorem original_tape_cons (a : m.core.Γ m.core.k₀) (word : List (m.core.Γ m.core.k₀)) :
    Function.update (initList m.core word).stk m.core.k₀ (a::word) =
      (initList m.core (a::word)).stk := by
  funext k
  by_cases h : k = m.core.k₀
  · subst k; simp [initList]
  · simp [initList,h]

theorem scan_left (a : m.core.Γ m.core.k₀)
    (input : List (m.core.Γ m.core.k₀ ⊕ Bool))
    (original : List (m.core.Γ m.core.k₀)) (bits : List Bool) (n : ℕ) :
    (computer m T acceptControl).step
      (scanCfg m T acceptControl false (.inl a::input) original bits n) =
        some (scanCfg m T acceptControl false input (a::original) bits (n+1)) := by
  have h : Nonempty (m.core.Γ m.core.k₀) := ⟨a⟩
  simp [FinTM2.step,TM2.step,computer,program,scanCfg,scanner,TM2.stepAux,
    pushOriginal,h,rawLeft,setRaw,scratchState,setSeen,initial,resetScratch,oldState,
    tapes,raw,originalBuffer,SumStacks.merge,SumStacks.update_left,SumStacks.update_right,
    HeterogeneousSum.merge,HeterogeneousSum.update_left,extras_update_raw,
    extras_update_original,extras,wordTape,Function.update_idem,List.replicate_succ]

theorem scan_right (seen : Bool) (b : Bool)
    (input : List (m.core.Γ m.core.k₀ ⊕ Bool))
    (original : List (m.core.Γ m.core.k₀)) (bits : List Bool) (n : ℕ) :
    (computer m T acceptControl).step
      (scanCfg m T acceptControl seen (.inr b::input) original bits n) =
        some (scanCfg m T acceptControl true input original (b::bits) n) := by
  simp [FinTM2.step,TM2.step,computer,program,scanCfg,scanner,TM2.stepAux,
    rawLeft,rawRight,setRaw,scratchState,setSeen,initial,resetScratch,oldState,
    tapes,raw,packetBuffer,SumStacks.merge,SumStacks.update_right,
    HeterogeneousSum.merge,HeterogeneousSum.update_left,extras_update_raw,
    extras_update_packet,extras]

theorem scan_bad_order (a : m.core.Γ m.core.k₀)
    (input : List (m.core.Γ m.core.k₀ ⊕ Bool))
    (original : List (m.core.Γ m.core.k₀)) (bits : List Bool) (n : ℕ) :
    (computer m T acceptControl).step
      (scanCfg m T acceptControl true (.inl a::input) original bits n) =
        some (HeterogeneousSum.restateCfg (Alphabet m T) (cleanupStates m T)
          (clean m T) none
          (Cleanup.cfg (Alphabet m T) (raw m T) (raw m T) Sum.inr 0 false
            (Function.update
              (scanCfg m T acceptControl true (.inl a::input) original bits n).stk
              (raw m T) input))) := by
  simp [FinTM2.step,TM2.step,computer,program,scanCfg,scanner,TM2.stepAux,
    rawLeft,setRaw,scratchState,setSeen,initial,resetScratch,oldState,
    tapes,raw,SumStacks.merge,HeterogeneousSum.merge,extras,finish,
    HeterogeneousSum.restateCfg,Cleanup.cfg]

theorem scan_original_prefix (word original : List (m.core.Γ m.core.k₀))
    (suffix : List (m.core.Γ m.core.k₀ ⊕ Bool)) (bits : List Bool) (n : ℕ) :
    (fun p => p.bind (computer m T acceptControl).step)^[word.length]
      (some (scanCfg m T acceptControl false (word.map Sum.inl++suffix) original bits n)) =
        some (scanCfg m T acceptControl false suffix (word.reverse++original) bits (n+word.length)) := by
  induction word generalizing original n with
  | nil => simp
  | cons a word ih =>
    rw [List.length_cons,List.map_cons,List.cons_append,Function.iterate_succ_apply,
      Option.bind_some,scan_left]
    simpa [List.reverse_cons,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
      using ih (a::original) (n+1)

theorem scan_right_prefix (bits packetReverse : List Bool)
    (suffix : List (m.core.Γ m.core.k₀ ⊕ Bool))
    (original : List (m.core.Γ m.core.k₀)) (n : ℕ) :
    (fun p => p.bind (computer m T acceptControl).step)^[bits.length]
      (some (scanCfg m T acceptControl true (bits.map Sum.inr++suffix) original packetReverse n)) =
        some (scanCfg m T acceptControl true suffix original (bits.reverse++packetReverse) n) := by
  induction bits generalizing packetReverse with
  | nil => simp
  | cons b bits ih =>
    rw [List.length_cons,List.map_cons,List.cons_append,Function.iterate_succ_apply,
      Option.bind_some,scan_right]
    simpa [List.reverse_cons,List.append_assoc] using ih (b::packetReverse)

theorem scan_nil (seen : Bool) (original : List (m.core.Γ m.core.k₀))
    (bits : List Bool) (n : ℕ) :
    (computer m T acceptControl).step (scanCfg m T acceptControl seen [] original bits n) =
      some (originalCfg m T acceptControl seen original bits n []) := by
  simp [FinTM2.step,TM2.step,computer,program,scanCfg,originalCfg,scanner,TM2.stepAux,
    setRaw,scratchState,setSeen,initial,resetScratch,oldState,tapes,raw,
    SumStacks.merge,SumStacks.update_right,HeterogeneousSum.merge,
    HeterogeneousSum.update_left,extras_update_raw,extras,initList]
  congr 3
  funext k
  split_ifs with h
  · subst k; rfl
  · rfl

def afterBits (seen : Bool) (bits : List Bool) : Bool := if bits = [] then seen else true

theorem scan_bits (seen : Bool) (bits packetReverse : List Bool)
    (original : List (m.core.Γ m.core.k₀)) (n : ℕ) :
    (fun p => p.bind (computer m T acceptControl).step)^[bits.length+1]
      (some (scanCfg m T acceptControl seen (bits.map Sum.inr) original packetReverse n)) =
        some (originalCfg m T acceptControl (afterBits seen bits) original
          (bits.reverse++packetReverse) n []) := by
  induction bits generalizing seen packetReverse with
  | nil => simpa [afterBits] using scan_nil m T acceptControl seen original packetReverse n
  | cons b bits ih =>
    rw [List.length_cons,List.map_cons,Function.iterate_succ_apply,Option.bind_some,
      scan_right]
    simpa [afterBits,List.reverse_cons,List.append_assoc] using ih true (b::packetReverse)

theorem scan_fields (word : List (m.core.Γ m.core.k₀)) (bits : List Bool)
    (originalReverse : List (m.core.Γ m.core.k₀)) (n : ℕ) :
    (fun p => p.bind (computer m T acceptControl).step)^[word.length+bits.length+1]
      (some (scanCfg m T acceptControl false (word.map Sum.inl++bits.map Sum.inr)
        originalReverse [] n)) =
        some (originalCfg m T acceptControl (afterBits false bits)
          (word.reverse++originalReverse) bits.reverse (n+word.length) []) := by
  induction word generalizing originalReverse n with
  | nil => simpa using scan_bits m T acceptControl false bits [] originalReverse n
  | cons a word ih =>
    rw [List.length_cons,List.map_cons,List.cons_append]
    rw [show word.length+1+bits.length+1 = (word.length+bits.length+1)+1 by omega,
      Function.iterate_succ_apply,Option.bind_some,scan_left]
    simpa [List.reverse_cons,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
      using ih (a::originalReverse) (n+1)

theorem original_cons (seen : Bool) (a : m.core.Γ m.core.k₀)
    (original word : List (m.core.Γ m.core.k₀)) (bits : List Bool) (n : ℕ) :
    (computer m T acceptControl).step
      (originalCfg m T acceptControl seen (a::original) bits n word) =
        some (originalCfg m T acceptControl seen original bits n (a::word)) := by
  have h : Nonempty (m.core.Γ m.core.k₀) := ⟨a⟩
  simp [FinTM2.step,TM2.step,computer,program,originalCfg,scanner,TM2.stepAux,
    pushOriginal,h,setOriginal,scratchState,setSeen,initial,resetScratch,oldState,
    tapes,originalBuffer,originalInput,SumStacks.merge,SumStacks.update_right,
    HeterogeneousSum.merge,HeterogeneousSum.update_left,HeterogeneousSum.update_right,
    extras_update_original,extras,original_tape_cons]
  have hi : (initList m.core word).stk m.core.k₀ = word := by simp [initList]
  rw [hi, original_tape_cons]

theorem original_nil (seen : Bool) (word : List (m.core.Γ m.core.k₀))
    (bits : List Bool) (n : ℕ) :
    (computer m T acceptControl).step (originalCfg m T acceptControl seen [] bits n word) =
      some (packetCfg m T acceptControl seen bits n word []) := by
  simp [FinTM2.step,TM2.step,computer,program,originalCfg,packetCfg,scanner,TM2.stepAux,
    setOriginal,scratchState,setSeen,initial,resetScratch,oldState,tapes,originalBuffer,
    SumStacks.merge,SumStacks.update_right,HeterogeneousSum.merge,
    HeterogeneousSum.update_left,extras_update_original,extras]

theorem original_run (seen : Bool) (original word : List (m.core.Γ m.core.k₀))
    (bits : List Bool) (n : ℕ) :
    (fun p => p.bind (computer m T acceptControl).step)^[original.length+1]
      (some (originalCfg m T acceptControl seen original bits n word)) =
        some (packetCfg m T acceptControl seen bits n (original.reverse++word) []) := by
  induction original generalizing word with
  | nil => simpa using original_nil m T acceptControl seen word bits n
  | cons a original ih =>
    rw [List.length_cons,Function.iterate_succ_apply,Option.bind_some,original_cons]
    simpa [List.reverse_cons,List.append_assoc] using ih (a::word)

theorem packet_cons (seen b : Bool) (bits packetWord : List Bool)
    (n : ℕ) (word : List (m.core.Γ m.core.k₀)) :
    (computer m T acceptControl).step
      (packetCfg m T acceptControl seen (b::bits) n word packetWord) =
        some (packetCfg m T acceptControl seen bits n word (b::packetWord)) := by
  simp [FinTM2.step,TM2.step,computer,program,packetCfg,scanner,TM2.stepAux,
    setBit,scratchState,setSeen,initial,resetScratch,oldState,tapes,packetBuffer,packet,
    SumStacks.merge,SumStacks.update_right,HeterogeneousSum.merge,
    HeterogeneousSum.update_left,HeterogeneousSum.update_right,
    extras_update_packet,extras,Reverse.Program.word_update]
  rw [SumStacks.update_left, Reverse.Program.word_update]

theorem packet_nil (seen : Bool) (packetWord : List Bool)
    (n : ℕ) (word : List (m.core.Γ m.core.k₀)) :
    (computer m T acceptControl).step (packetCfg m T acceptControl seen [] n word packetWord) =
      some (clockCfg m T acceptControl word packetWord
        (initList (clock T).computer (List.replicate n true))) := by
  rw [Machine.init_eq]
  simp [FinTM2.step,TM2.step,computer,program,packetCfg,clockCfg,scanner,TM2.stepAux,
    setBit,scratchState,setSeen,initial,tapes,packetBuffer,SumStacks.leftCfg,embedCfg,
    clockLayout,clockStates,SumStacks.merge,SumStacks.update_right,HeterogeneousSum.merge,
    HeterogeneousSum.update_left,extras_update_packet,extras]

theorem packet_transfer_run (seen : Bool) (bits packetWord : List Bool)
    (n : ℕ) (word : List (m.core.Γ m.core.k₀)) :
    (fun p => p.bind (computer m T acceptControl).step)^[bits.length+1]
      (some (packetCfg m T acceptControl seen bits n word packetWord)) =
        some (clockCfg m T acceptControl word (bits.reverse++packetWord)
          (initList (clock T).computer (List.replicate n true))) := by
  induction bits generalizing packetWord with
  | nil => simpa using packet_nil m T acceptControl seen packetWord n word
  | cons b bits ih =>
    rw [List.length_cons,Function.iterate_succ_apply,Option.bind_some,packet_cons]
    simpa [List.reverse_cons,List.append_assoc] using ih (b::packetWord)

/-- Actual initial raw field encoding to the actual unary-clock input,
with both original fields restored byte-for-byte in separate physical tapes. -/
theorem raw_staging (word : List (m.core.Γ m.core.k₀)) (bits : List Bool) :
    (fun p => p.bind (computer m T acceptControl).step)^[2*(word.length+bits.length)+3]
      (some (initList (computer m T acceptControl)
        (word.map Sum.inl++bits.map Sum.inr))) =
        some (clockCfg m T acceptControl word bits
          (initList (clock T).computer (List.replicate word.length true))) := by
  rw [← initial_raw]
  have hs := scan_fields m T acceptControl word bits [] 0
  have ho := original_run m T acceptControl (afterBits false bits) word.reverse []
    bits.reverse word.length
  have hp := packet_transfer_run m T acceptControl (afterBits false bits) bits.reverse [] word.length word
  simp only [List.append_nil,Nat.zero_add,List.reverse_reverse,List.length_reverse] at hs ho hp
  rw [show 2*(word.length+bits.length)+3 =
    (bits.length+1)+(word.length+1)+(word.length+bits.length+1) by omega,
    Function.iterate_add_apply,Function.iterate_add_apply,hs,ho,hp]

theorem clock_step (word : List (m.core.Γ m.core.k₀)) (bits : List Bool)
    (c d : (clock T).Config) (h : (clock T).computer.step c = some d) :
    (computer m T acceptControl).step (clockCfg m T acceptControl word bits c) =
      some (clockCfg m T acceptControl word bits d) := by
  rcases c with ⟨l,v,S⟩
  cases l with
  | none => simp [FinTM2.step,TM2.step] at h
  | some l =>
    have hd : TM2.stepAux ((clock T).program l) v S = d := Option.some.inj h
    subst d
    simp only [FinTM2.step,TM2.step,clockCfg,SumStacks.leftCfg,embedCfg,Option.elim_some,
      computer,program,SumStacks.left_stepAux,embed_stepAux]

theorem clock_iterate (n : ℕ) (word : List (m.core.Γ m.core.k₀)) (bits : List Bool)
    (c d : (clock T).Config)
    (h : (fun p => p.bind (clock T).computer.step)^[n] (some c) = some d) :
    (fun p => p.bind (computer m T acceptControl).step)^[n]
      (some (clockCfg m T acceptControl word bits c)) =
        some (clockCfg m T acceptControl word bits d) := by
  induction n generalizing d with
  | zero =>
    have hd : c = d := Option.some.inj h
    subst d
    rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply'] at h
    cases hp : (fun p => p.bind (clock T).computer.step)^[n] (some c) with
    | none => simp only [hp, Option.bind_none] at h; cases h
    | some previous =>
      have hs : (clock T).computer.step previous = some d := by simpa only [hp, Option.bind_some] using h
      rw [Function.iterate_succ_apply',ih previous hp,Option.bind_some]
      exact clock_step m T acceptControl word bits previous d hs

theorem clock_run (word : List (m.core.Γ m.core.k₀)) (bits : List Bool) :
    (fun p => p.bind (computer m T acceptControl).step)^[((clockComputes T).outputs word.length).steps]
      (some (clockCfg m T acceptControl word bits
        (initList (clock T).computer (List.replicate word.length true)))) =
        some (clockCfg m T acceptControl word bits
          (haltList (clock T).computer (List.replicate (T.eval word.length) true))) := by
  apply clock_iterate
  have h := ((clockComputes T).outputs word.length).evals_in_steps
  simp only [Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.RuntimeParameters.unary,
    UnaryBinary.unaryEncoding, Option.map_some] at h
  convert h using 1 <;> rfl

end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Reverse.Staging.Program
