import Holant.Proofs.CountingMachines.StandardMachine.Support.BooleanOpcode.NativeExecution

set_option backward.isDefEq.respectTransparency false
/-! Locally checked adaptation of the frozen reference proof. Sole Boolean-opcode entry. The complete symbol/statement
compiler and coded-path bijection are proved from the original actual machine.
The native witness capstone consumes the installed raw-byte preparation and
real output decoder: complete fixed-clock physical accepting paths biject the
same original accepted witnesses, with internally produced time/capacity/cost
bounds. Arbitrary finite input serialization and identification with an
independently chosen conventional #P model remain separate boundaries. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.BooleanOpcode.Source
open Turing Computability Holant.Complexity
variable (m : BinaryMachine)

abbrev codedMachine := Compiler.machine m

theorem coded_statement (q : m.core.Stmt) (v : m.core.σ) (S : ∀ k, List (m.core.Γ k)) :
    TM2.stepAux (Compiler.statement m q) (Block.clear m v) (Code.tapes m S) =
      Compiler.cfg m (TM2.stepAux q v S) := Compiler.statement_stepAux m q v S

def coded_paths_equiv (n : ℕ) (c d : m.Config) :
    Compiler.Path m n c d ≃ Compiler.CodedPath m n c d := Compiler.pathsEquiv m n c d

theorem coded_paths_count (n : ℕ) (c d : m.Config) :
    Fintype.card (Compiler.Path m n c d) = Fintype.card (Compiler.CodedPath m n c d) :=
  Compiler.paths_count m n c d

theorem statement_primitive (q : m.core.Stmt) (v : Block.State m) (S : m.core.K → List Bool) :
    (HeterogeneousCost.execute (Compiler.statement m q) v S).1 ≤
      Compiler.coefficient m*HeterogeneousCost.budget q := Compiler.statement_primitive m q v S

theorem coded_prefix_bits (T : Polynomial ℕ) (word : List (m.core.Γ m.core.k₀))
    (log : List Bool) (j : ℕ) (next : List Bool × (codedMachine m).Config)
    (hj : j ≤ T.eval word.length)
    (hr : (codedMachine m).run j (log,initList (codedMachine m).core (Code.word m m.core.k₀ word)) = some next) :
    (codedMachine m).codedStorageBits next.2 ≤ (Compiler.bitsPolynomial m T).eval word.length :=
  Compiler.prefix_bits m T word log j next hj hr

/-- This constructor builds real all-Bool tables. It does not accept a
simulator, an execution proof, a count law, or a desired accepting flag. -/
def nativeMachine (trueSymbol : m.core.Γ m.core.k₁)
    (inputAlphabet : m.core.Γ m.core.k₀ ≃ Bool) : BinaryMachine :=
  NativeFinish.machine m trueSymbol inputAlphabet

theorem native_prepare (trueSymbol : m.core.Γ m.core.k₁)
    (inputAlphabet : m.core.Γ m.core.k₀ ≃ Bool) (word : List Bool) :
    (fun p => p.bind (nativeMachine m trueSymbol inputAlphabet).core.step)^[
      NativeInput.steps (Output.observed m trueSymbol) word.length]
      (some (initList (nativeMachine m trueSymbol inputAlphabet).core word)) =
        some (NativeFinish.cfg m trueSymbol inputAlphabet
          (NativeInput.sourceCfg (Output.observed m trueSymbol) inputAlphabet
            (Compiler.cfg (Output.observed m trueSymbol)
              (initList (Output.observed m trueSymbol).core (word.map inputAlphabet.symm))))) :=
  NativeFinish.prepare m trueSymbol inputAlphabet word

theorem native_decode_true (trueSymbol : m.core.Γ m.core.k₁)
    (inputAlphabet : m.core.Γ m.core.k₀ ≃ Bool) :
    (nativeMachine m trueSymbol inputAlphabet).core.step
      (NativeFinish.decoderEntry m trueSymbol inputAlphabet) =
        some (haltList (nativeMachine m trueSymbol inputAlphabet).core [true]) :=
  NativeFinish.decoder_step m trueSymbol inputAlphabet

/-- Concrete native metadata comes from the existing witness machine itself:
its input alphabet is genuinely Bool, and its true symbol is the old actual
outputAlphabet.symm (Sum.inr true), not an externally supplied desired value. -/
def witnessMachine {α : Type} {ea : Encoding α Bool} {f : α → ℕ} (w : SharpPWitness ea f) : BinaryMachine :=
  nativeMachine (Reverse.TapeAcceptance.Forward.original w)
    (Reverse.TapeAcceptance.Forward.trueSymbol w) (Equiv.refl Bool)

theorem witness_prepare {α : Type} {ea : Encoding α Bool} {f : α → ℕ}
    (w : SharpPWitness ea f) (word : List Bool) :
    (fun p => p.bind (witnessMachine w).core.step)^[
      NativeInput.steps (Reverse.TapeAcceptance.Forward.observed w) word.length]
      (some (initList (witnessMachine w).core word)) =
        some (NativeFinish.cfg (Reverse.TapeAcceptance.Forward.original w)
          (Reverse.TapeAcceptance.Forward.trueSymbol w) (Equiv.refl Bool)
          (NativeInput.sourceCfg (Reverse.TapeAcceptance.Forward.observed w) (Equiv.refl Bool)
            (Compiler.cfg (Reverse.TapeAcceptance.Forward.observed w)
              (initList (Reverse.TapeAcceptance.Forward.observed w).core word)))) := by
  simpa only [witnessMachine,Equiv.refl_symm,Equiv.coe_refl,List.map_id] using native_prepare (Reverse.TapeAcceptance.Forward.original w)
    (Reverse.TapeAcceptance.Forward.trueSymbol w) (Equiv.refl Bool) word

def observed_tape_equiv {α : Type} {ea : Encoding α Bool} {f : α → ℕ}
    (w : SharpPWitness ea f) (a : α) :
    Compiler.Path (Reverse.TapeAcceptance.Forward.observed w)
      (Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Source.time w a)
      (initList (Reverse.TapeAcceptance.Forward.observed w).core (ea.encode a))
      (Reverse.TapeAcceptance.Program.liftCfg (Reverse.TapeAcceptance.Forward.original w)
        (Reverse.TapeAcceptance.Forward.trueSymbol w)
        (haltList (Reverse.TapeAcceptance.Forward.original w).core
          [Reverse.TapeAcceptance.Forward.trueSymbol w])) ≃
        Reverse.TapeAcceptance.Program.TapePath (Reverse.TapeAcceptance.Forward.original w)
          (Reverse.TapeAcceptance.Forward.trueSymbol w)
          (Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Source.time w a)
          (initList (Reverse.TapeAcceptance.Forward.original w).core (ea.encode a)) where
  toFun p := ⟨p.val,(Reverse.TapeAcceptance.Program.trace_lift_iff
    (Reverse.TapeAcceptance.Forward.original w) (Reverse.TapeAcceptance.Forward.trueSymbol w)
    _ _ _).mp (by simpa only [Reverse.TapeAcceptance.Program.lift_init (Reverse.TapeAcceptance.Forward.original w) (Reverse.TapeAcceptance.Forward.trueSymbol w)] using p.property)⟩
  invFun p := ⟨p.val,by
    simpa only [Reverse.TapeAcceptance.Program.lift_init (Reverse.TapeAcceptance.Forward.original w) (Reverse.TapeAcceptance.Forward.trueSymbol w)] using
      (Reverse.TapeAcceptance.Program.trace_lift_iff (Reverse.TapeAcceptance.Forward.original w)
        (Reverse.TapeAcceptance.Forward.trueSymbol w) _ _ _).mpr p.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

/-- The coded-state interface is retained alongside the strengthened raw
native capstone below, without changing its programme or token convention. -/
def forward_coded_accepted_equiv {α : Type} {ea : Encoding α Bool} {f : α → ℕ}
    (w : SharpPWitness ea f) (a : α) :
    Compiler.CodedPath (Reverse.TapeAcceptance.Forward.observed w)
      (Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Source.time w a)
      (initList (Reverse.TapeAcceptance.Forward.observed w).core (ea.encode a))
      (Reverse.TapeAcceptance.Program.liftCfg (Reverse.TapeAcceptance.Forward.original w)
        (Reverse.TapeAcceptance.Forward.trueSymbol w)
        (haltList (Reverse.TapeAcceptance.Forward.original w).core
          [Reverse.TapeAcceptance.Forward.trueSymbol w])) ≃
        Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Source.AcceptedWitness w a :=
  (Compiler.pathsEquiv (Reverse.TapeAcceptance.Forward.observed w) _ _ _).symm.trans
    ((observed_tape_equiv w a).trans ((Reverse.TapeAcceptance.Forward.tapePhysicalEquiv w a).trans
      (Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Source.acceptedWitnessPhysicalEquiv w a).symm))

theorem forward_coded_count {α : Type} {ea : Encoding α Bool} {f : α → ℕ}
    (w : SharpPWitness ea f) (a : α) :
    Fintype.card (Compiler.CodedPath (Reverse.TapeAcceptance.Forward.observed w)
      (Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Source.time w a)
      (initList (Reverse.TapeAcceptance.Forward.observed w).core (ea.encode a))
      (Reverse.TapeAcceptance.Program.liftCfg (Reverse.TapeAcceptance.Forward.original w)
        (Reverse.TapeAcceptance.Forward.trueSymbol w)
        (haltList (Reverse.TapeAcceptance.Forward.original w).core
          [Reverse.TapeAcceptance.Forward.trueSymbol w]))) = f a := by
  rw [Fintype.card_congr (forward_coded_accepted_equiv w a),
    Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Source.accepted_witness_card]
  exact (w.counts a).symm

abbrev nativeTimePolynomial {α : Type} {ea : Encoding α Bool} {f : α → ℕ}
    (w : SharpPWitness ea f) := NativeExecution.timePolynomial w
abbrev nativeCapacityPolynomial {α : Type} {ea : Encoding α Bool} {f : α → ℕ}
    (w : SharpPWitness ea f) := NativeExecution.capacityPolynomial w
abbrev nativePrimitivePolynomial {α : Type} {ea : Encoding α Bool} {f : α → ℕ}
    (w : SharpPWitness ea f) := NativeExecution.primitivePolynomial w
abbrev nativeBitsPolynomial {α : Type} {ea : Encoding α Bool} {f : α → ℕ}
    (w : SharpPWitness ea f) := NativeExecution.bitsPolynomial w
abbrev nativeInternalBitsPolynomial {α : Type} {ea : Encoding α Bool} {f : α → ℕ}
    (w : SharpPWitness ea f) := NativeExecution.internalBitsPolynomial w
abbrev NativePhysicalPath {α : Type} {ea : Encoding α Bool} {f : α → ℕ}
    (w : SharpPWitness ea f) (a : α) := NativeExecution.PhysicalPath w a

theorem native_clock {α : Type} {ea : Encoding α Bool} {f : α → ℕ}
    (w : SharpPWitness ea f) (a : α) :
    (nativeTimePolynomial w).eval (ea.encode a).length =
      NativeInput.steps (Reverse.TapeAcceptance.Forward.observed w) (ea.encode a).length+
        (Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Source.time w a+1) := NativeExecution.time_eq w a

/-- The only inputs are the original witness and original input. Physical
paths start at the same ea.encode a, not at a supplied encoded configuration. -/
def native_accepted_equiv {α : Type} {ea : Encoding α Bool} {f : α → ℕ}
    (w : SharpPWitness ea f) (a : α) :
    Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Source.AcceptedWitness w a ≃ NativePhysicalPath w a :=
  NativeExecution.acceptedEquiv w a

theorem native_physical_count {α : Type} {ea : Encoding α Bool} {f : α → ℕ}
    (w : SharpPWitness ea f) (a : α) : Fintype.card (NativePhysicalPath w a) = f a :=
  NativeExecution.physical_count w a

theorem native_accepts_iff {α : Type} {ea : Encoding α Bool} {f : α → ℕ}
    (w : SharpPWitness ea f) (a : α) (log : List Bool) :
    (witnessMachine w).run ((nativeTimePolynomial w).eval (ea.encode a).length)
      (log,initList (witnessMachine w).core (ea.encode a)) =
        some ([],haltList (witnessMachine w).core [true]) ↔
      log.length = Holant.LocalDrafts.CountingHardness.VerifierRun.witnessLength w a ∧ w.accept (a,log.reverse) = true :=
  (NativeExecution.accepts_iff w a log).trans
    (Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Source.accepts_iff w a log)

theorem native_tokens_preserved {α : Type} {ea : Encoding α Bool} {f : α → ℕ}
    (w : SharpPWitness ea f) (a : α) (p : Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Source.PhysicalPath w a) :
    (NativeExecution.physicalEquiv w a p).val =
      List.replicate (NativeInput.steps (Reverse.TapeAcceptance.Forward.observed w) (ea.encode a).length) none++
        p.val++[none] := NativeExecution.tokens_preserved w a p

theorem native_choices_exact {α : Type} {ea : Encoding α Bool} {f : α → ℕ}
    (w : SharpPWitness ea f) (a : α) (p : NativePhysicalPath w a) :
    (p.val.filterMap id).length = Holant.LocalDrafts.CountingHardness.VerifierRun.witnessLength w a ∧
      w.accept (a,(p.val.filterMap id).reverse) = true := NativeExecution.choices_exact w a p

theorem native_statement_prefix {α : Type} {ea : Encoding α Bool} {f : α → ℕ}
    (w : SharpPWitness ea f) (b : Bool) (l : (witnessMachine w).core.Λ)
    (v : (witnessMachine w).core.σ) (S : (witnessMachine w).core.K → List Bool) :
    let q := NativeFinish.program (Reverse.TapeAcceptance.Forward.original w)
      (Reverse.TapeAcceptance.Forward.trueSymbol w) (Equiv.refl Bool) b l
    NativeExecution.PrimitivePrefix q v S (HeterogeneousCost.execute q v S).1
      (TM2.stepAux q v S).var (TM2.stepAux q v S).stk :=
  NativeExecution.primitive_full _ v S

/-- Actual execution, every macro prefix's primitive cost and all tape/control
bits, bounded in the length of the same original raw input encoding. -/
theorem native_actual_prefix {α : Type} {ea : Encoding α Bool} {f : α → ℕ}
    (w : SharpPWitness ea f) (a : α) (p : NativePhysicalPath w a) (j : ℕ)
    (hj : j ≤ (nativeTimePolynomial w).eval (ea.encode a).length) :
    ∃ next : List Bool × (witnessMachine w).Config,
      (witnessMachine w).run j (p.val.filterMap id,initList (witnessMachine w).core (ea.encode a)) = some next ∧
      (∀ k, (next.2.stk k).length ≤ (nativeCapacityPolynomial w).eval (ea.encode a).length) ∧
      (witnessMachine w).primitiveCost j (p.val.filterMap id,initList (witnessMachine w).core (ea.encode a)) ≤
        (nativePrimitivePolynomial w).eval (ea.encode a).length ∧
      (witnessMachine w).codedStorageBits next.2 ≤ (nativeBitsPolynomial w).eval (ea.encode a).length := by
  obtain ⟨next,hr⟩ := NativeExecution.prefix_run w a p j hj
  exact ⟨next,hr,NativeExecution.prefix_capacity w a _ j next hj hr,
    NativeExecution.prefix_primitive w a _ j hj,NativeExecution.prefix_bits w a _ j next hj hr⟩

/-- The proof-only PrimitivePrefix records each actual push/pop/peek/load/test
inside the installed table. The extra one charges a possible split choice. -/
theorem native_internal_prefix {α : Type} {ea : Encoding α Bool} {f : α → ℕ}
    (w : SharpPWitness ea f) (a : α) (log : List Bool) (j : ℕ)
    (next : List Bool × (witnessMachine w).Config)
    (hj : j < (nativeTimePolynomial w).eval (ea.encode a).length)
    (hr : (witnessMachine w).run j (log,initList (witnessMachine w).core (ea.encode a)) = some next)
    (l : (witnessMachine w).core.Λ) (hl : next.2.l = some l) (b : Bool)
    (n : ℕ) (u : (witnessMachine w).core.σ) (U : (witnessMachine w).core.K → List Bool)
    (h : NativeExecution.PrimitivePrefix
      (NativeFinish.program (Reverse.TapeAcceptance.Forward.original w)
        (Reverse.TapeAcceptance.Forward.trueSymbol w) (Equiv.refl Bool) b l)
      next.2.var next.2.stk n u U) (control : Option (witnessMachine w).core.Λ) :
    (witnessMachine w).primitiveCost j (log,initList (witnessMachine w).core (ea.encode a))+(n+1) ≤
      (nativePrimitivePolynomial w).eval (ea.encode a).length ∧
    (witnessMachine w).codedStorageBits ⟨control,u,U⟩ ≤
      (nativeInternalBitsPolynomial w).eval (ea.encode a).length :=
  NativeExecution.internal_prefix w a log j next hj hr l hl b n u U h control

/-- Sole raw native forward capstone. This is a statement about the explicit
BinaryMachine held-edge presentation, not conventional #P model equivalence. -/
theorem witness_native {α : Type} {ea : Encoding α Bool} {f : α → ℕ}
    (w : SharpPWitness ea f) (a : α) :
    Nonempty (Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Source.AcceptedWitness w a ≃ NativePhysicalPath w a) ∧
      Fintype.card (NativePhysicalPath w a) = f a :=
  ⟨⟨native_accepted_equiv w a⟩,native_physical_count w a⟩

end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.BooleanOpcode.Source
