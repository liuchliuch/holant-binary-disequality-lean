import Holant.Proofs.CountingMachines.StandardMachine.Support.GeneralAlphabetInput.NativeExecution

set_option backward.isDefEq.respectTransparency false
/-! Adapted reference proof. See the task validation reports. General finite-alphabet bounded-path counting entry.
The original machine, its original polynomial clock, its finite acceptance
table and its original input encoding internally produce a standard
SharpPWitness. The verifier is the delivered physical heterogeneous staging
programme, not an evaluation callback. Canonical packets have exactly two
bits per original edge; their bijection with actual original paths and the
same native programme's accepted packet witnesses is consumed below.
No Γinput ≃ Bool, supplied SharpPWitness, verifier law, count equality or
independent conventional #P model-equivalence premise is accepted. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.GeneralAlphabetSharpWitness
open Turing Computability Holant.Complexity
open Reverse.Staging

namespace Native
export GeneralAlphabetInput.NativeExecution
  (native time timePolynomial capacityPolynomial primitivePolynomial bitsPolynomial
    native_accepts_iff canonical_trace actual_prefix)
end Native

variable (m : BinaryMachine) (T : Polynomial ℕ) (acceptControl : m.core.σ → Bool)
local instance : Fintype m.core.K := m.core.kFin
local instance : Fintype m.core.Λ := m.core.ΛFin
local instance : Fintype m.core.σ := m.core.σFin
local instance (key : m.core.K) : Fintype (m.core.Γ key) := m.alphabets key
variable {α : Type} (ea : Encoding α (m.core.Γ m.core.k₀))

def clock (a : α) : ℕ := T.eval (ea.encode a).length
def start (a : α) : m.Config := initList m.core (ea.encode a)
def accepts (p : α × List Bool) : Bool :=
  Program.packetEval m acceptControl (clock m T ea p.1) p.2 (start m ea p.1)

/-- The target count was already the cardinality of real original m.step
paths. It is not defined through the new witness predicate. -/
def boundedCount (a : α) : ℕ := Program.pathCount m acceptControl ea T a
abbrev OriginalPath (a : α) :=
  Program.AcceptedPath m acceptControl (clock m T ea a) (start m ea a)
abbrev PacketWitness (a : α) :=
  Program.AcceptedBits m acceptControl (clock m T ea a) (start m ea a)

/-- Sole original-alphabet constructor. All four fields have internal
producers: actual staging verifier and its canonical path/packet bijection. -/
def source : SharpPWitness ea (boundedCount m T acceptControl ea) where
  witnessLength := 2*T
  accept := accepts m T acceptControl ea
  verifier := Program.verifier m T acceptControl ea
  counts a := by
    simpa only [boundedCount,accepts,clock,start,Polynomial.eval_mul,Polynomial.eval_ofNat]
      using Program.path_count m acceptControl ea T a

theorem inSharpP : InSharpP ea (boundedCount m T acceptControl ea) :=
  ⟨source m T acceptControl ea⟩

@[simp] theorem witness_length (a : α) :
    (source m T acceptControl ea).witnessLength.eval (ea.encode a).length =
      2*clock m T ea a := by
  simp only [source,Polynomial.eval_mul,Polynomial.eval_ofNat,clock]

@[simp] theorem same_original_machine :
    (source m T acceptControl ea).verifier.tm = Program.computer m T acceptControl := rfl

/-- Raw original tagged fields physically feed the old unary polynomial
clock. This producer exposes T(original Γ length), before packet execution;
it does not install a host polynomial evaluation or count serialized bits. -/
theorem initialize_clock (a : α) (bits : List Bool) :
    (fun p => p.bind (source m T acceptControl ea).verifier.tm.step)^[
      ((Program.clockComputes T).outputs (ea.encode a).length).steps+
        (2*((ea.encode a).length+bits.length)+3)]
      (some (initList (source m T acceptControl ea).verifier.tm
        ((ea.encode a).map Sum.inl++bits.map Sum.inr))) =
      some (Program.readyCfg m T acceptControl (clock m T ea a) bits (start m ea a)) := by
  dsimp only [source,Program.verifier]
  rw [Function.iterate_add_apply,Program.raw_staging,Program.clock_run,Program.clock_terminal]
  rfl

def verifier_outputs (a : α) (bits : List Bool) :
    TM2OutputsInTime (source m T acceptControl ea).verifier.tm
      ((ea.encode a).map Sum.inl++bits.map Sum.inr)
      (some [Sum.inr (accepts m T acceptControl ea (a,bits))])
      ((Program.timePolynomial m T acceptControl).eval ((ea.encode a).length+bits.length)) :=
  Program.outputs m T acceptControl (ea.encode a) bits

/-- The source acceptance predicate is justified by whole physical execution
on the original Γ⊕Bool input tape and whole clean standard Γ⊕Bool output. -/
theorem physical_accepts_iff (a : α) (bits : List Bool) :
    (∃ steps, (fun p => p.bind (source m T acceptControl ea).verifier.tm.step)^[steps]
      (some (initList (source m T acceptControl ea).verifier.tm
        ((ea.encode a).map Sum.inl++bits.map Sum.inr))) =
          some (haltList (source m T acceptControl ea).verifier.tm [Sum.inr true])) ↔
      accepts m T acceptControl ea (a,bits) = true :=
  (Reverse.Staging.Source.physical_accepts_iff m T acceptControl (ea.encode a) bits).trans
    (Program.packet_accepts_iff m acceptControl _ bits _).symm

/-- This is the old packet proof's genuine two-way map, retaining every
original edge token. Its inverse rejects malformed/noncanonical choices. -/
def packetsEquiv (a : α) : PacketWitness m T acceptControl ea a ≃
    OriginalPath m T acceptControl ea a :=
  Program.acceptedEquiv m acceptControl _ _

theorem packet_word (a : α) (p : OriginalPath m T acceptControl ea a) :
    List.ofFn (Program.pathToBits m acceptControl _ _ p).val =
      (List.ofFn p.val).flatMap Reverse.Packet.encode :=
  Program.pathBits_word m acceptControl _ p

theorem same_count (a : α) :
    boundedCount m T acceptControl ea a =
      witnessCount ((source m T acceptControl ea).witnessLength.eval (ea.encode a).length)
        (fun bits => (source m T acceptControl ea).accept (a,bits)) :=
  (source m T acceptControl ea).counts a

/-- Reification executes the SAME original machine for exactly T(N) edges.
The physical staging/native bounds never replace this clock by T(rawBits). -/
theorem original_execution (a : α) (p : OriginalPath m T acceptControl ea a) :
    ∃ d, m.run (clock m T ea a)
        ((List.ofFn p.val).filterMap id,start m ea a) = some ([],d) ∧
      m.tokensOfRun (clock m T ea a)
        ((List.ofFn p.val).filterMap id,start m ea a) = List.ofFn p.val ∧
      d.l = none ∧ acceptControl d.var = true :=
  Reverse.Staging.Source.path_execution m T acceptControl ea a p

theorem ordinary_token_unique (label : m.core.Λ) (c d : m.Config)
    (token : Option Bool) (hl : c.l = some label) (hs : m.split label = false)
    (h : m.step token c = some d) : token = none := by
  cases token with
  | none => rfl
  | some bit => simp [BinaryMachine.step,hl,hs] at h

theorem halted_token_unique (c d : m.Config) (token : Option Bool)
    (hc : c.l = none) (h : m.step token c = some d) : token = none := by
  cases token with
  | none => rfl
  | some bit => simp [BinaryMachine.step,hc] at h

@[simp] theorem deterministic_packet : Reverse.Packet.encode none = [false,false] := rfl
@[simp] theorem false_branch_packet : Reverse.Packet.encode (some false) = [true,false] := rfl
@[simp] theorem true_branch_packet : Reverse.Packet.encode (some true) = [true,true] := rfl

theorem wrong_length_rejected (a : α) (bits : List Bool)
    (h : bits.length ≠ 2*clock m T ea a) : accepts m T acceptControl ea (a,bits) = false :=
  Reverse.Staging.Source.wrong_length_rejected m acceptControl _ bits _ h

theorem illegal_packet_rejected (n : ℕ) (rest : List Bool) (c : m.Config) :
    Program.packetEval m acceptControl (n+1) (false::true::rest) c = false :=
  Reverse.Staging.Source.illegal_packet_rejected m acceptControl n rest c

/-- Native acceptance is observed on the same literal Γ-tagged serialization,
not on a freely supplied prepared memory or known result symbol. -/
theorem native_accepts_iff (a : α) (bits : List Bool) :
    (Native.native m T acceptControl).run
      (Native.time m T acceptControl (ea.encode a) bits)
      ([],initList (Native.native m T acceptControl).core
        (GeneralAlphabetInput.raw m T acceptControl (ea.encode a) bits)) =
          some ([],haltList (Native.native m T acceptControl).core [true]) ↔
      accepts m T acceptControl ea (a,bits) = true :=
  (Native.native_accepts_iff m T acceptControl (ea.encode a) bits).trans
    (Program.packet_accepts_iff m acceptControl _ bits _).symm

abbrev NativePacketWitness (a : α) :=
  {bits : Fin (2*clock m T ea a) → Bool //
    (Native.native m T acceptControl).run
      (Native.time m T acceptControl (ea.encode a) (List.ofFn bits))
      ([],initList (Native.native m T acceptControl).core
        (GeneralAlphabetInput.raw m T acceptControl (ea.encode a) (List.ofFn bits))) =
          some ([],haltList (Native.native m T acceptControl).core [true])}

def packetsNativeEquiv (a : α) : PacketWitness m T acceptControl ea a ≃
    NativePacketWitness m T acceptControl ea a where
  toFun p := ⟨p.val,(native_accepts_iff m T acceptControl ea a _).mpr p.property⟩
  invFun p := ⟨p.val,(native_accepts_iff m T acceptControl ea a _).mp p.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

def pathsNativeEquiv (a : α) : OriginalPath m T acceptControl ea a ≃
    NativePacketWitness m T acceptControl ea a :=
  (packetsEquiv m T acceptControl ea a).symm.trans (packetsNativeEquiv m T acceptControl ea a)

noncomputable instance nativePacketsFintype (a : α) :
    Fintype (NativePacketWitness m T acceptControl ea a) :=
  Fintype.ofEquiv (OriginalPath m T acceptControl ea a) (pathsNativeEquiv m T acceptControl ea a)

theorem native_count (a : α) :
    Fintype.card (NativePacketWitness m T acceptControl ea a) = boundedCount m T acceptControl ea a := by
  rw [Fintype.card_congr (pathsNativeEquiv m T acceptControl ea a).symm]
  rfl

theorem native_tokens_canonical (a : α) (bits : List Bool) :
    (Native.native m T acceptControl).TraceValid
      (List.replicate (Native.time m T acceptControl (ea.encode a) bits) none)
      (initList (Native.native m T acceptControl).core
        (GeneralAlphabetInput.raw m T acceptControl (ea.encode a) bits))
      (haltList (Native.native m T acceptControl).core [accepts m T acceptControl ea (a,bits)]) :=
  Native.canonical_trace m T acceptControl (ea.encode a) bits

/-- At fixed witness length the total tagged input length is N+2T(N).
Composition here concerns mathematical bounds only; no polynomial evaluator
is installed as an opcode. The old physical clock still reads original N. -/
def taggedLengthPolynomial : Polynomial ℕ := Polynomial.X+2*T
def witnessTimePolynomial : Polynomial ℕ :=
  (Program.timePolynomial m T acceptControl).comp (taggedLengthPolynomial T)
def witnessCapacityPolynomial : Polynomial ℕ :=
  (Program.capacityPolynomial m T acceptControl).comp (taggedLengthPolynomial T)
def witnessPrimitivePolynomial : Polynomial ℕ :=
  (Program.primitivePolynomial m T acceptControl).comp (taggedLengthPolynomial T)
def witnessBitsPolynomial : Polynomial ℕ :=
  (Program.bitsPolynomial m T acceptControl).comp (taggedLengthPolynomial T)

theorem tagged_length (a : α) (bits : Fin (2*clock m T ea a) → Bool) :
    (ea.encode a).length+(List.ofFn bits).length =
      (taggedLengthPolynomial T).eval (ea.encode a).length := by
  simp only [List.length_ofFn,taggedLengthPolynomial,Polynomial.eval_add,
    Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_ofNat,clock]

theorem witness_time (a : α) (bits : Fin (2*clock m T ea a) → Bool) :
    (Program.outputs m T acceptControl (ea.encode a) (List.ofFn bits)).steps ≤
      (witnessTimePolynomial m T acceptControl).eval (ea.encode a).length := by
  calc
    _ ≤ (Program.timePolynomial m T acceptControl).eval
        ((ea.encode a).length + (List.ofFn bits).length) :=
      (Program.outputs m T acceptControl (ea.encode a) (List.ofFn bits)).steps_le_m
    _ = _ := by
      rw [tagged_length m T ea a bits]
      simp only [witnessTimePolynomial, Polynomial.eval_comp]

theorem actual_prefix (a : α) (bits : Fin (2*clock m T ea a) → Bool) (j : ℕ)
    (hj : j ≤ (Program.outputs m T acceptControl (ea.encode a) (List.ofFn bits)).steps) :
    ∃ next, (fun p => p.bind (source m T acceptControl ea).verifier.tm.step)^[j]
      (some (initList (source m T acceptControl ea).verifier.tm
        ((ea.encode a).map Sum.inl++(List.ofFn bits).map Sum.inr))) = some next ∧
      (∀ key, (next.stk key).length ≤
        (witnessCapacityPolynomial m T acceptControl).eval (ea.encode a).length) ∧
      (Program.deterministic m T acceptControl).codedStorageBits next ≤
        (witnessBitsPolynomial m T acceptControl).eval (ea.encode a).length ∧
      (Program.deterministic m T acceptControl).primitiveCost j
        ([],initList (source m T acceptControl ea).verifier.tm
          ((ea.encode a).map Sum.inl++(List.ofFn bits).map Sum.inr)) ≤
            (witnessPrimitivePolynomial m T acceptControl).eval (ea.encode a).length := by
  have h := Reverse.Staging.Source.actual_prefix m T acceptControl
    (ea.encode a) (List.ofFn bits) j hj
  rw [tagged_length m T ea a bits] at h
  simpa only [source,Program.verifier,witnessCapacityPolynomial,witnessPrimitivePolynomial,
    witnessBitsPolynomial,Polynomial.eval_comp] using h

/-- Only the bound is composed with the serialization length. The SAME
native programme still physically counts original Γ symbols and runs T(N). -/
def serializedLengthPolynomial : Polynomial ℕ :=
  Polynomial.C (GeneralAlphabetInput.rawWidth m T acceptControl)*taggedLengthPolynomial T
def nativeWitnessTimePolynomial : Polynomial ℕ :=
  (Native.timePolynomial m T acceptControl).comp (serializedLengthPolynomial m T acceptControl)
def nativeWitnessCapacityPolynomial : Polynomial ℕ :=
  (Native.capacityPolynomial m T acceptControl).comp (serializedLengthPolynomial m T acceptControl)
def nativeWitnessPrimitivePolynomial : Polynomial ℕ :=
  (Native.primitivePolynomial m T acceptControl).comp (serializedLengthPolynomial m T acceptControl)
def nativeWitnessBitsPolynomial : Polynomial ℕ :=
  (Native.bitsPolynomial m T acceptControl).comp (serializedLengthPolynomial m T acceptControl)

theorem serialized_length (a : α) (bits : Fin (2*clock m T ea a) → Bool) :
    (GeneralAlphabetInput.raw m T acceptControl (ea.encode a) (List.ofFn bits)).length =
      (serializedLengthPolynomial m T acceptControl).eval (ea.encode a).length := by
  rw [GeneralAlphabetInput.raw_length,tagged_length m T ea a bits]
  simp only [serializedLengthPolynomial,Polynomial.eval_mul,Polynomial.eval_C]

theorem native_witness_time (a : α) (bits : Fin (2*clock m T ea a) → Bool) :
    Native.time m T acceptControl (ea.encode a) (List.ofFn bits) =
      (nativeWitnessTimePolynomial m T acceptControl).eval (ea.encode a).length := by
  rw [Native.time,serialized_length m T acceptControl ea a bits]
  simp only [nativeWitnessTimePolynomial,Polynomial.eval_comp]

theorem native_actual_prefix (a : α) (bits : Fin (2*clock m T ea a) → Bool) (j : ℕ)
    (hj : j ≤ (nativeWitnessTimePolynomial m T acceptControl).eval (ea.encode a).length) :
    ∃ next, (Native.native m T acceptControl).run j
      ([],initList (Native.native m T acceptControl).core
        (GeneralAlphabetInput.raw m T acceptControl (ea.encode a) (List.ofFn bits))) = some next ∧
      (∀ key, (next.2.stk key).length ≤
        (nativeWitnessCapacityPolynomial m T acceptControl).eval (ea.encode a).length) ∧
      (Native.native m T acceptControl).primitiveCost j
        ([],initList (Native.native m T acceptControl).core
          (GeneralAlphabetInput.raw m T acceptControl (ea.encode a) (List.ofFn bits))) ≤
            (nativeWitnessPrimitivePolynomial m T acceptControl).eval (ea.encode a).length ∧
      (Native.native m T acceptControl).codedStorageBits next.2 ≤
        (nativeWitnessBitsPolynomial m T acceptControl).eval (ea.encode a).length := by
  have hj' : j ≤ Native.time m T acceptControl (ea.encode a) (List.ofFn bits) := by
    rw [native_witness_time m T acceptControl ea a bits]
    exact hj
  have h := Native.actual_prefix m T acceptControl (ea.encode a) (List.ofFn bits) [] j hj'
  rw [serialized_length m T acceptControl ea a bits] at h
  simpa only [nativeWitnessCapacityPolynomial,nativeWitnessPrimitivePolynomial,
    nativeWitnessBitsPolynomial,Polynomial.eval_comp] using h

end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.GeneralAlphabetSharpWitness
