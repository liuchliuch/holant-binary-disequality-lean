import Holant.Proofs.CountingMachines.StandardMachine.Support.ConventionalSharpPSource

set_option backward.isDefEq.respectTransparency false
/-!
Locally checked adaptation of the frozen reference proof. All-raw-input finite nondeterministic guess/verify source.
The existing total parser/bounded-packet verifier, whose input codec is identity
on ALL List Bool, is the verifier supplied to the existing native forward
program constructor. Its actual computation, not the old promise restricted to
ea.encode a, proves termination for every word and every sequence of choices.

The accepted original witness -> old native path -> actual observer path ->
canonical packet -> checked false suffix -> new native path maps are all
internally produced bijections. Runtime code never tests an arbitrary ea image.
Malformed means failure of the existing strict fixed-block original-list-code
parser. On a grammar-valid word outside an arbitrary semantic ea image, the
count is the actual bounded old-program count; it is not silently set to zero.

This closes the all-input clock obligation for the finite Boolean-stack TM2
presentation. It does not identify an independently defined ordinary tape-TM
transition system with this program, or rename this result conventional #P.
-/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.TotalRawSource
open Turing Computability Holant.Complexity

namespace Base
export ConventionalSharpPSource
  (source rawInput observedSource nativeClock observedAccept totalReverse reverseInput
    AcceptedWitness AcceptingPath acceptingPathEquiv paddedWitnessEquiv booleanWitness
    tapePhysicalEquiv total_reverse_count)
end Base
namespace Total
export GeneralAlphabetTotalInput
  (originalWitness input_code codeWord totalCount accepts parsedWord malformed_zero malformed_rejected)
end Total
namespace PacketModel
export GeneralAlphabetSharpWitness
  (clock start OriginalPath PacketWitness packetsEquiv packet_word witness_length)
end PacketModel
namespace Native
export BooleanOpcode.NativeExecution
  (entry decoded decoded_halt prepare_run run_after time_eq prefix_capacity prefix_primitive prefix_bits)
end Native
namespace Observer
export Reverse.TapeAcceptance.Program (TapePath tapeControlEquiv lift_init)
end Observer

private def acceptedCast {n m : ℕ} (h : n = m) (A : List Bool → Bool) :
    {bits : Fin n → Bool // A (List.ofFn bits) = true} ≃
      {bits : Fin m → Bool // A (List.ofFn bits) = true} where
  toFun p := ⟨fun i => p.val (Fin.cast h.symm i),by
    rw [← List.ofFn_congr h p.val]
    exact p.property⟩
  invFun p := ⟨fun i => p.val (Fin.cast h i),by
    rw [← List.ofFn_congr h.symm p.val]
    exact p.property⟩
  left_inv p := by
    apply Subtype.ext
    funext i
    exact congrArg p.val (by apply Fin.ext; rfl)
  right_inv p := by
    apply Subtype.ext
    funext i
    exact congrArg p.val (by apply Fin.ext; rfl)

variable {α Γ : Type} [Fintype Γ] {ea : Encoding α Γ} {f : α → ℕ}
variable (w : SharpPWitness ea f)

/-- Internally generated ALL-word verifier: strict physical parser, actual
polynomial counter, bounded packet interpreter and whole-stack cleanup. -/
abbrev verifier := Base.totalReverse w
abbrev rawValue := Total.totalCount (Base.observedSource w) (Base.nativeClock w) (Base.observedAccept w)

/-- Sole source constructor, consuming the already delivered real native
guess/verify tables on the total verifier. There is no new interpreter. -/
def source : BinaryMachine := BooleanOpcode.Source.witnessMachine (verifier w)
abbrev timePolynomial := BooleanOpcode.Source.nativeTimePolynomial (verifier w)
abbrev capacityPolynomial := BooleanOpcode.Source.nativeCapacityPolynomial (verifier w)
abbrev primitivePolynomial := BooleanOpcode.Source.nativePrimitivePolynomial (verifier w)
abbrev bitsPolynomial := BooleanOpcode.Source.nativeBitsPolynomial (verifier w)
abbrev internalBitsPolynomial := BooleanOpcode.Source.nativeInternalBitsPolynomial (verifier w)
def horizon (word : List Bool) : ℕ := (timePolynomial w).eval word.length
def choiceLength (word : List Bool) : ℕ := Holant.LocalDrafts.CountingHardness.VerifierRun.witnessLength (verifier w) word
abbrev old := Reverse.TapeAcceptance.Forward.original (verifier w)
abbrev symbol := Reverse.TapeAcceptance.Forward.trueSymbol (verifier w)

theorem choice_length (word : List Bool) :
    choiceLength w word = 2*(Base.nativeClock w).eval word.length :=
  PacketModel.witness_length (Base.observedSource w) (Base.nativeClock w) (Base.observedAccept w)
    (encodingList Bool) word

theorem clock_eq (word : List Bool) : horizon w word =
    BooleanOpcode.NativeInput.steps (Reverse.TapeAcceptance.Forward.observed (verifier w)) word.length+
      (Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Source.time (verifier w) word+1) :=
  Native.time_eq (verifier w) word

def terminal (word choices : List Bool) : (source w).Config :=
  Native.decoded (old w) (symbol w) (Equiv.refl Bool)
    (WitnessMachine.terminal (verifier w) ((verifier w).accept (word,choices.reverse)))

theorem terminal_halts (word choices : List Bool) : (terminal w word choices).l = none :=
  Native.decoded_halt (old w) (symbol w) (Equiv.refl Bool) _

/-- The actual raw preparation and source/decoder clocks, before any verdict
is known. The only runtime input is word, on the literal native input stack. -/
private theorem run_formula (word log : List Bool) :
    (source w).run (horizon w word) (log,initList (source w).core word) =
      ((old w).run (Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Source.time (verifier w) word)
        (log,initList (old w).core word)).bind (fun s =>
          if s.2.l.isNone then some (s.1,Native.decoded (old w) (symbol w) (Equiv.refl Bool) s.2)
          else (source w).advance (s.1,Native.entry (old w) (symbol w) (Equiv.refl Bool) s.2)) := by
  have ht := Native.time_eq (verifier w) word
  change horizon w word =
    BooleanOpcode.NativeInput.steps (Reverse.TapeAcceptance.Forward.observed (verifier w)) word.length+
      (Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Source.time (verifier w) word+1) at ht
  rw [ht,Nat.add_comm,BinaryMachine.run_add]
  have hp : (source w).run
      (BooleanOpcode.NativeInput.steps (Reverse.TapeAcceptance.Forward.observed (verifier w)) word.length)
      (log,initList (source w).core word) =
        some (log,Native.entry (old w) (symbol w) (Equiv.refl Bool) (initList (old w).core word)) := by
    convert Native.prepare_run (old w) (symbol w) (Equiv.refl Bool) word log using 1 <;>
      (try rfl) <;> simp [Equiv.refl,Equiv.symm]
  rw [hp,Option.bind_some]
  exact Native.run_after (old w) (symbol w) (Equiv.refl Bool)
    (Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Source.time (verifier w) word) log (initList (old w).core word)

/-- ALL raw words, ALL choices, either verdict. No parser success, original
ea image, accepted endpoint or verifier-computes premise is an argument. -/
theorem all_raw_run (word choices rest : List Bool) (hlen : choices.length = choiceLength w word) :
    (source w).run (horizon w word) (choices++rest,initList (source w).core word) =
      some (rest,terminal w word choices) := by
  have hh : (WitnessMachine.terminal (verifier w) ((verifier w).accept (word,choices.reverse))).l.isNone = true := rfl
  have hp := Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Source.padded_run
    (verifier w) word choices rest hlen
  change (old w).run (Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Source.time (verifier w) word)
    (choices++rest,initList (old w).core word) =
    some (rest,WitnessMachine.terminal (verifier w) ((verifier w).accept (word,choices.reverse))) at hp
  rw [run_formula,hp]
  rfl

theorem all_raw_halt (word : List Bool) (choices : Fin (choiceLength w word) → Bool) :
    ∃ d : (source w).Config, d.l = none ∧
      (source w).run (horizon w word) (List.ofFn choices,initList (source w).core word) = some ([],d) := by
  refine ⟨terminal w word (List.ofFn choices),terminal_halts w _ _,?_⟩
  simpa only [List.append_nil] using all_raw_run w word (List.ofFn choices) [] (List.length_ofFn)

/-- The log observer erases to real labelled machine edges. Thus the ALL-word
run receipt produces physical paths, with no runtime branch-log input tape. -/
theorem all_raw_trace (word : List Bool) (choices : Fin (choiceLength w word) → Bool) :
    ∃ tokens d, tokens.length = horizon w word ∧ tokens.filterMap id = List.ofFn choices ∧
      (source w).TraceValid tokens (initList (source w).core word) d ∧ d.l = none := by
  obtain ⟨d,hd,hr⟩ := all_raw_halt w word choices
  obtain ⟨tokens,hlen,hlog,htrace⟩ := (source w).run_trace (horizon w word)
    (List.ofFn choices,initList (source w).core word) ([],d) hr
  exact ⟨tokens,d,hlen,by simpa only [List.append_nil] using hlog,htrace,hd⟩

/-- A short mathematical branch log cannot name a complete real path. The
actual machine does not read such a log as an input or invent its missing bits. -/
theorem short_log_fails (word log : List Bool) (hlen : log.length < choiceLength w word) :
    (source w).run (horizon w word) (log,initList (source w).core word) = none := by
  have hp := Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Source.short_log_fails
    (verifier w) word log hlen
  change (old w).run (Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Source.time (verifier w) word)
    (log,initList (old w).core word) = none at hp
  rw [run_formula,hp,Option.bind_none]

/-- Every physical trace reaching the constructed deadline has halted and
has used precisely the actual counter's number of split choices, accepting
or rejecting. The configuration and the choice count are consequences. -/
theorem all_paths_halt (word : List Bool) (tokens : List (Option Bool)) (d : (source w).Config)
    (hlen : tokens.length = horizon w word)
    (htrace : (source w).TraceValid tokens (initList (source w).core word) d) :
    d.l = none ∧ (tokens.filterMap id).length = choiceLength w word := by
  let log := tokens.filterMap id
  have hr := ((source w).reify_trace tokens _ _ htrace).1
  rw [hlen] at hr
  have hge : choiceLength w word ≤ log.length := by
    by_contra hnot
    have hbad := short_log_fails w word log (by omega)
    rw [hbad] at hr
    cases hr
  let first := log.take (choiceLength w word)
  let rest := log.drop (choiceLength w word)
  have hfirst : first.length = choiceLength w word := by
    simp only [first,List.length_take,Nat.min_eq_left hge]
  have hsplit : first++rest = log := List.take_append_drop _ _
  have hfull := all_raw_run w word first rest hfirst
  rw [hsplit] at hfull
  have hend : (rest,terminal w word first) = ([],d) := Option.some.inj (hfull.symm.trans hr)
  have hd : terminal w word first = d := congrArg Prod.snd hend
  have hrest : rest = [] := congrArg Prod.fst hend
  have hz := congrArg List.length hrest
  simp only [rest,List.length_drop,List.length_nil] at hz
  exact ⟨hd ▸ terminal_halts w word first,by change log.length = _; omega⟩

/-- Any longer real held trace is already at the same halted configuration;
all its post-deadline tokens are the sole None padding. -/
theorem after_deadline (word : List Bool) (tokens : List (Option Bool)) (d : (source w).Config)
    (hlen : horizon w word ≤ tokens.length)
    (htrace : (source w).TraceValid tokens (initList (source w).core word) d) :
    d.l = none ∧ tokens.drop (horizon w word) =
      List.replicate (tokens.drop (horizon w word)).length none := by
  obtain ⟨middle,hfirst,hrest⟩ := (BooleanOpcode.NativeExecution.trace_append (source w)
    (tokens.take (horizon w word)) (tokens.drop (horizon w word)) _ _).mp
      (by simpa only [List.take_append_drop] using htrace)
  have htake : (tokens.take (horizon w word)).length = horizon w word := by
    simp only [List.length_take,Nat.min_eq_left hlen]
  have hm := (all_paths_halt w word _ middle htake hfirst).1
  have hhold := (BooleanOpcode.NativeExecution.trace_halt_iff (source w) _ middle d hm).mp hrest
  exact ⟨hhold.1 ▸ hm,hhold.2⟩

/-- All real prefixes, including malformed/rejecting input paths. Their run
equation is internally reified from their actual step equations. -/
theorem all_path_resources (word : List Bool) (tokens : List (Option Bool)) (d : (source w).Config)
    (hlen : tokens.length ≤ horizon w word)
    (htrace : (source w).TraceValid tokens (initList (source w).core word) d) :
    (∀ k, (d.stk k).length ≤ (capacityPolynomial w).eval word.length) ∧
      (source w).primitiveCost tokens.length
        (tokens.filterMap id,initList (source w).core word) ≤ (primitivePolynomial w).eval word.length ∧
      (source w).codedStorageBits d ≤ (bitsPolynomial w).eval word.length := by
  have hr := ((source w).reify_trace tokens _ _ htrace).1
  exact ⟨Native.prefix_capacity (verifier w) word _ _ ([],d) hlen hr,
    Native.prefix_primitive (verifier w) word _ _ hlen,
    Native.prefix_bits (verifier w) word _ _ ([],d) hlen hr⟩

theorem all_choice_prefix (word choices rest : List Bool) (hlen : choices.length = choiceLength w word)
    (j : ℕ) (hj : j ≤ horizon w word) :
    ∃ next : List Bool × (source w).Config,
      (source w).run j (choices++rest,initList (source w).core word) = some next ∧
      (∀ k, (next.2.stk k).length ≤ (capacityPolynomial w).eval word.length) ∧
      (source w).primitiveCost j (choices++rest,initList (source w).core word) ≤
        (primitivePolynomial w).eval word.length ∧
      (source w).codedStorageBits next.2 ≤ (bitsPolynomial w).eval word.length := by
  obtain ⟨next,hr⟩ := (source w).prefix_exists (horizon w word) j _ _
    (all_raw_run w word choices rest hlen) hj
  exact ⟨next,hr,Native.prefix_capacity (verifier w) word _ j next hj hr,
    Native.prefix_primitive (verifier w) word _ j hj,Native.prefix_bits (verifier w) word _ j next hj hr⟩

def statement (b : Bool) (l : (source w).core.Λ) :=
  BooleanOpcode.NativeFinish.program (old w) (symbol w) (Equiv.refl Bool) b l

theorem all_internal_prefix (word log : List Bool) (j : ℕ)
    (next : List Bool × (source w).Config) (hj : j < horizon w word)
    (hr : (source w).run j (log,initList (source w).core word) = some next)
    (l : (source w).core.Λ) (hl : next.2.l = some l) (b : Bool)
    (n : ℕ) (u : (source w).core.σ) (U : (source w).core.K → List Bool)
    (h : BooleanOpcode.NativeExecution.PrimitivePrefix (statement w b l) next.2.var next.2.stk n u U)
    (control : Option (source w).core.Λ) :
    (source w).primitiveCost j (log,initList (source w).core word)+(n+1) ≤
      (primitivePolynomial w).eval word.length ∧
    (source w).codedStorageBits ⟨control,u,U⟩ ≤ (internalBitsPolynomial w).eval word.length :=
  BooleanOpcode.Source.native_internal_prefix (verifier w) word log j next hj hr l hl b n u U h control

abbrev AcceptingPath (word : List Bool) := BooleanOpcode.Source.NativePhysicalPath (verifier w) word
def count (word : List Bool) : ℕ := Fintype.card (AcceptingPath w word)

theorem raw_count (word : List Bool) : count w word = rawValue w word :=
  BooleanOpcode.Source.native_physical_count (verifier w) word

def acceptedRawEquiv (word : List Bool) :
    Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Source.AcceptedWitness (verifier w) word ≃ AcceptingPath w word :=
  BooleanOpcode.Source.native_accepted_equiv (verifier w) word

theorem canonical_tokens (word : List Bool)
    (p : Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Source.PhysicalPath (verifier w) word) :
    (BooleanOpcode.NativeExecution.physicalEquiv (verifier w) word p).val =
      List.replicate (BooleanOpcode.NativeInput.steps
        (Reverse.TapeAcceptance.Forward.observed (verifier w)) word.length) none ++ p.val ++ [none] :=
  BooleanOpcode.Source.native_tokens_preserved (verifier w) word p

theorem malformed_count (word : List Bool)
    (hp : GeneralAlphabetTotalInput.Parser.parse
      (Base.observedSource w) (Base.nativeClock w) (Base.observedAccept w) word = none) :
    count w word = 0 := (raw_count w word).trans (Total.malformed_zero _ _ _ word hp)

/-- Physical acceptance is impossible, rather than just a numerical zero. -/
theorem malformed_no_path (word : List Bool)
    (hp : GeneralAlphabetTotalInput.Parser.parse
      (Base.observedSource w) (Base.nativeClock w) (Base.observedAccept w) word = none) :
    IsEmpty (AcceptingPath w word) := by
  refine ⟨fun p => ?_⟩
  have ha := (BooleanOpcode.Source.native_choices_exact (verifier w) word p).2
  have hf := Total.malformed_rejected (Base.observedSource w) (Base.nativeClock w)
    (Base.observedAccept w) word (p.val.filterMap id).reverse hp
  change (verifier w).accept (word,(p.val.filterMap id).reverse) = false at hf
  exact Bool.noConfusion (hf.symm.trans ha)

/-- The old observer's false flag is produced from the actual clean false
terminal and the old true-terminal injection. It is not a decoder premise. -/
private theorem rejecting_head (word choices : List Bool)
    (hf : (verifier w).accept (word,choices.reverse) = false) :
    ((terminal w word choices).stk (source w).core.k₁).head? = some false := by
  have hflag : Reverse.TapeAcceptance.Program.acceptControl (old w)
      (Reverse.TapeAcceptance.Program.liftCfg (old w) (symbol w)
        (WitnessMachine.terminal (verifier w) false)).var = false := by
    cases h : Reverse.TapeAcceptance.Program.acceptControl (old w)
        (Reverse.TapeAcceptance.Program.liftCfg (old w) (symbol w)
          (WitnessMachine.terminal (verifier w) false)).var with
    | false => rfl
    | true =>
        have ht := (Reverse.TapeAcceptance.Program.endpoint_accepts_iff (old w) (symbol w)
          (WitnessMachine.terminal (verifier w) false)).mp ⟨rfl,h⟩
        have he : WitnessMachine.terminal (verifier w) false = WitnessMachine.terminal (verifier w) true :=
          ht.trans (WitnessMachine.terminal_eq_halt (verifier w) true).symm
        have hbad : false = true := Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Source.terminal_injective (verifier w) he
        cases hbad
  unfold terminal
  rw [hf]
  exact BooleanOpcode.NativeExecution.decoded_rejects_flag
    (old w) (symbol w) (Equiv.refl Bool) (WitnessMachine.terminal (verifier w) false) hflag

/-- ALL malformed words and ALL chronological guesses really halt with a
false output head; acceptance also has no physical path by malformed_no_path. -/
theorem malformed_halt (word : List Bool) (choices : Fin (choiceLength w word) → Bool)
    (hp : GeneralAlphabetTotalInput.Parser.parse
      (Base.observedSource w) (Base.nativeClock w) (Base.observedAccept w) word = none) :
    ∃ d : (source w).Config, d.l = none ∧ (d.stk (source w).core.k₁).head? = some false ∧
      (source w).run (horizon w word) (List.ofFn choices,initList (source w).core word) = some ([],d) := by
  have hf : (verifier w).accept (word,(List.ofFn choices).reverse) = false :=
    Total.malformed_rejected _ _ _ word (List.ofFn choices).reverse hp
  refine ⟨terminal w word (List.ofFn choices),terminal_halts w _ _,rejecting_head w _ _ hf,?_⟩
  simpa only [List.append_nil] using all_raw_run w word (List.ofFn choices) [] (List.length_ofFn)

def encodedInput (a : α) : List Bool := Base.reverseInput w a
local instance : Fintype ((Base.observedSource w).core.Γ (Base.observedSource w).core.k₀) :=
  (Base.observedSource w).alphabets (Base.observedSource w).core.k₀

abbrev wordWitness := Total.originalWitness (Base.observedSource w) (Base.nativeClock w) (Base.observedAccept w)
abbrev paddedWordWitness := Base.booleanWitness (wordWitness w)
def baseClock (a : α) : ℕ := (Base.nativeClock w).eval (Base.rawInput w a).length

/-- The actual old output observer retains the same tokens and reads all
tapes itself. No desired accepting-control equivalence is a source premise. -/
def controlEquiv (a : α) :
    Observer.TapePath (Base.source w) true (baseClock w a)
      (initList (Base.source w).core (Base.rawInput w a)) ≃
    PacketModel.OriginalPath (Base.observedSource w) (Base.nativeClock w) (Base.observedAccept w)
      (encodingList Bool) (Base.rawInput w a) where
  toFun p := ⟨p.val,by
    have hp := (Reverse.TapeAcceptance.Program.accepts_trace_iff (Base.source w) true
      (List.ofFn p.val) (initList (Base.source w).core (Base.rawInput w a))).mpr p.property
    simpa only [Observer.lift_init,GeneralAlphabetSharpWitness.start,encodingList,id_eq] using hp⟩
  invFun p := ⟨p.val,by
    apply (Reverse.TapeAcceptance.Program.accepts_trace_iff (Base.source w) true
      (List.ofFn p.val) (initList (Base.source w).core (Base.rawInput w a))).mp
    simpa only [Observer.lift_init,GeneralAlphabetSharpWitness.start,encodingList,id_eq] using p.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

def basePacketEquiv (a : α) : Base.AcceptingPath w a ≃
    PacketModel.PacketWitness (Base.observedSource w) (Base.nativeClock w) (Base.observedAccept w)
      (encodingList Bool) (Base.rawInput w a) :=
  (Base.tapePhysicalEquiv w a).symm.trans ((controlEquiv w a).trans
    (PacketModel.packetsEquiv (Base.observedSource w) (Base.nativeClock w) (Base.observedAccept w)
      (encodingList Bool) (Base.rawInput w a)).symm)

/-- None/false/true are the old actual 00/10/11 packets. Every edge and every
early-halt None survives; the forbidden 01 is not an extra accepting choice. -/
theorem packet_word (a : α) (p : Base.AcceptingPath w a) :
    List.ofFn (basePacketEquiv w a p).val = p.val.flatMap Reverse.Packet.encode := by
  let q := (controlEquiv w a) ((Base.tapePhysicalEquiv w a).symm p)
  have ht : List.ofFn q.val = p.val := by
    change List.ofFn ((Base.tapePhysicalEquiv w a).symm p).val = p.val
    exact congrArg Subtype.val ((Base.tapePhysicalEquiv w a).apply_symm_apply p)
  have hp := PacketModel.packet_word (Base.observedSource w) (Base.nativeClock w) (Base.observedAccept w)
    (encodingList Bool) (Base.rawInput w a) q
  change List.ofFn (basePacketEquiv w a p).val = (List.ofFn q.val).flatMap Reverse.Packet.encode at hp
  rw [ht] at hp
  exact hp

def packetWitnessEquiv (a : α) :
    PacketModel.PacketWitness (Base.observedSource w) (Base.nativeClock w) (Base.observedAccept w)
      (encodingList Bool) (Base.rawInput w a) ≃
    Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Source.AcceptedWitness (wordWitness w) (Base.rawInput w a) := by
  have h : 2*baseClock w a = Holant.LocalDrafts.CountingHardness.VerifierRun.witnessLength (wordWitness w) (Base.rawInput w a) :=
    (PacketModel.witness_length (Base.observedSource w) (Base.nativeClock w) (Base.observedAccept w)
      (encodingList Bool) (Base.rawInput w a)).symm
  exact acceptedCast h (fun bits => (wordWitness w).accept (Base.rawInput w a,bits))

/-- This equation is produced from the literal strict parser's parse_code
receipt and the actual generated verifier's accept field, not supplied. -/
theorem legal_accept (a : α) (bits : List Bool) :
    (verifier w).accept (encodedInput w a,bits) =
      (paddedWordWitness w).accept (Base.rawInput w a,bits) := by
  change GeneralAlphabetTotalInput.accepts (Base.observedSource w) (Base.nativeClock w) (Base.observedAccept w)
    (GeneralAlphabetTotalInput.codeWord (Base.observedSource w) (Base.nativeClock w)
      (Base.observedAccept w) (Base.rawInput w a),bits) =
        BooleanInputWitness.paddedAccept (wordWitness w) (Base.rawInput w a,bits)
  simp [GeneralAlphabetTotalInput.accepts,GeneralAlphabetTotalInput.parsedWord]

theorem candidate_length (a : α) :
    Holant.LocalDrafts.CountingHardness.VerifierRun.witnessLength (paddedWordWitness w) (Base.rawInput w a) =
      Holant.LocalDrafts.CountingHardness.VerifierRun.witnessLength (verifier w) (encodedInput w a) := by
  change (wordWitness w).witnessLength.eval
    ((BooleanInputWitness.inputEncoding (wordWitness w)).encode (Base.rawInput w a)).length =
      (wordWitness w).witnessLength.eval (encodedInput w a).length
  exact congrArg (fun bits : List Bool => (wordWitness w).witnessLength.eval bits.length)
    (Total.input_code (Base.observedSource w) (Base.nativeClock w) (Base.observedAccept w) (Base.rawInput w a))

def totalCandidateEquiv (a : α) :
    Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Source.AcceptedWitness (paddedWordWitness w) (Base.rawInput w a) ≃
      Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Source.AcceptedWitness (verifier w) (encodedInput w a) where
  toFun p := ⟨fun i => p.val (Fin.cast (candidate_length w a).symm i),by
    rw [legal_accept,← List.ofFn_congr (candidate_length w a) p.val]
    exact p.property⟩
  invFun p := ⟨fun i => p.val (Fin.cast (candidate_length w a) i),by
    rw [← legal_accept,← List.ofFn_congr (candidate_length w a).symm p.val]
    exact p.property⟩
  left_inv p := by
    apply Subtype.ext
    funext i
    exact congrArg p.val (by apply Fin.ext; rfl)
  right_inv p := by
    apply Subtype.ext
    funext i
    exact congrArg p.val (by apply Fin.ext; rfl)

/-- Every map is an actual already-produced path/packet/suffix map. The only
new transports change finite-vector indices by proved literal input lengths. -/
def encodedWitnessEquiv (a : α) : Base.AcceptedWitness w a ≃ AcceptingPath w (encodedInput w a) :=
  (Base.acceptingPathEquiv w a).trans ((basePacketEquiv w a).trans
    ((packetWitnessEquiv w a).trans ((Base.paddedWitnessEquiv (wordWitness w) (Base.rawInput w a)).trans
      ((totalCandidateEquiv w a).trans (acceptedRawEquiv w (encodedInput w a))))))

theorem encoded_count (a : α) : count w (encodedInput w a) = f a :=
  (raw_count w (encodedInput w a)).trans (Base.total_reverse_count w a)

/-- Faithful original input metadata; this semantic decoder is NEVER called
by source. The runtime domain remains all received Boolean words. -/
def inputEncoding : Encoding α Bool where
  encode := encodedInput w
  decode bits := (GeneralAlphabetTotalInput.Parser.parse
    (Base.observedSource w) (Base.nativeClock w) (Base.observedAccept w) bits).bind
      (fun word => (BooleanInputWitness.inputEncoding w).decode word)
  decode_encode a := by
    change (GeneralAlphabetTotalInput.Parser.parse (Base.observedSource w) (Base.nativeClock w)
      (Base.observedAccept w) (GeneralAlphabetTotalInput.codeWord (Base.observedSource w)
        (Base.nativeClock w) (Base.observedAccept w) (Base.rawInput w a))).bind _ = some a
    rw [GeneralAlphabetTotalInput.Parser.parse_code,Option.bind_some]
    exact Encoding.decode_encode (BooleanInputWitness.inputEncoding w) a

def encodedWidth : ℕ := GeneralAlphabetTotalInput.Parser.width
  (Base.observedSource w) (Base.nativeClock w) (Base.observedAccept w)*BooleanInputWitness.codeWidth w

theorem encoded_length (a : α) : (encodedInput w a).length = encodedWidth w*(ea.encode a).length := by
  change (GeneralAlphabetTotalInput.codeWord (Base.observedSource w) (Base.nativeClock w)
    (Base.observedAccept w) (Base.rawInput w a)).length = _
  rw [GeneralAlphabetTotalInput.Parser.code_length]
  unfold Base.rawInput
  rw [BooleanInputWitness.input_length w a]
  simp only [encodedWidth,Nat.mul_assoc]

def encodedTimePolynomial : Polynomial ℕ :=
  (timePolynomial w).comp (Polynomial.C (encodedWidth w)*Polynomial.X)

theorem encoded_time (a : α) : horizon w (encodedInput w a) =
    (encodedTimePolynomial w).eval (ea.encode a).length := by
  simp only [horizon,encodedTimePolynomial,Polynomial.eval_comp,Polynomial.eval_mul,
    Polynomial.eval_C,Polynomial.eval_X,encoded_length]

theorem encoded_resources (a : α) (tokens : List (Option Bool)) (d : (source w).Config)
    (hlen : tokens.length ≤ horizon w (encodedInput w a))
    (htrace : (source w).TraceValid tokens (initList (source w).core (encodedInput w a)) d) :
    (∀ k, (d.stk k).length ≤
      ((capacityPolynomial w).comp (Polynomial.C (encodedWidth w)*Polynomial.X)).eval (ea.encode a).length) ∧
    (source w).primitiveCost tokens.length (tokens.filterMap id,initList (source w).core (encodedInput w a)) ≤
      ((primitivePolynomial w).comp (Polynomial.C (encodedWidth w)*Polynomial.X)).eval (ea.encode a).length ∧
    (source w).codedStorageBits d ≤
      ((bitsPolynomial w).comp (Polynomial.C (encodedWidth w)*Polynomial.X)).eval (ea.encode a).length := by
  simpa only [Polynomial.eval_comp,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,← encoded_length]
    using all_path_resources w (encodedInput w a) tokens d hlen htrace

/-- Unique source capstone: actual ALL-word ND termination, strict malformed
zero, and original witness bijection/count on the internally encoded protocol.
No conventional-model equality or arbitrary ea-image decision is asserted. -/
theorem witness_source (a : α) :
    Nonempty (Base.AcceptedWitness w a ≃ AcceptingPath w (encodedInput w a)) ∧
      count w (encodedInput w a) = f a ∧
      (∀ (word : List Bool) (choices : Fin (choiceLength w word) → Bool),
        ∃ d : (source w).Config, d.l = none ∧
          (source w).run (horizon w word) (List.ofFn choices,initList (source w).core word) = some ([],d)) :=
  ⟨⟨encodedWitnessEquiv w a⟩,encoded_count w a,all_raw_halt w⟩

end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.TotalRawSource
