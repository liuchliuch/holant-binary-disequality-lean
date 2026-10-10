import Holant.Proofs.Dichotomy.Retained.StableHigherCurrentUnaryQueryBase

/-! Repaired actual-query control for the original-L pure-pin source.
This separate leaf preserves the failed original source and its diagnostics.
The old accessOriginalL and its existentially chosen Poly reduction are untouched.
V2 selects actual dichotomy NETWORK data, then installs the existing literal
one- or three-query program with an actual-prefix byte certificate. The original
two power macros, factor chain, ports, tables and field conversions are reused.
Fixed-family noncomputable installation is explicit; no uniform recognition-time
claim or Poly-to-LengthControlled coercion is made.
-/
noncomputable section
set_option maxHeartbeats 600000
set_option maxRecDepth 8192
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableHigherCurrentUnaryQueryControl
open Holant Holant.Tractable Holant.Algebraic Turing Computability
open Holant.Complexity BinaryCompose FixedFieldMachines OracleBatch StackProtocol
open Holant.LocalDrafts.Hardness
open Holant.LocalDrafts.Hardness.GeneralExtraction
open Holant.LocalDrafts.Hardness.FrozenFactorNormalization
open UniversalPairReduction FixedGadgetSubstitution
open Holant.LocalDrafts.MainChain

private theorem controlled_machine {α β γ δ ε ζ : Type}
    {ea : Encoding α Bool} {eb : Encoding β Bool}
    {ec : Encoding γ Bool} {ed : Encoding δ Bool}
    {ee : Encoding ε Bool} {ef : Encoding ζ Bool}
    {f : α → β} {g : γ → δ} {h : ε → ζ}
    (outer : LengthControlledOracleReduction ea eb ec ed f g)
    (inner : LengthControlledOracleReduction ec ed ee ef g h) :
    (outer.composeControlled inner).reduction.machine =
      OracleCompose.machine inner.reduction.machine outer.reduction.machine := rfl

private theorem query_origin_of_machine {α β γ δ ε ζ : Type}
    {ea : Encoding α Bool} {eb : Encoding β Bool}
    {ec : Encoding γ Bool} {ed : Encoding δ Bool}
    {ee : Encoding ε Bool} {ef : Encoding ζ Bool}
    {f : α → β} {g : γ → δ} {h : ε → ζ}
    (outer : LengthControlledOracleReduction ea eb ec ed f g)
    (inner : LengthControlledOracleReduction ec ed ee ef g h)
    (M : OracleMachine)
    (same : M = OracleCompose.machine inner.reduction.machine outer.reduction.machine)
    (oracle : List Bool → List Bool) (ho : RepresentsOracle ee ef h oracle)
    (x : α) (t : ℕ) (c : M.Cfg)
    (hr : M.run oracle (ea.encode x) t = some c) (hq : M.IsQuery c) :
    LengthControlledOracleReduction.CompositionQueryOrigin outer inner oracle x
      (cast (congrArg (fun machine : OracleMachine => machine.Cfg) same) c) := by
  subst M
  exact Holant.Complexity.ControlledComposition.query_origin outer inner oracle ho x t c hr hq

namespace Interpreter
variable {K : Type} [Field K] [Algebra ℚ K] {d s : ℕ} {A : ℕ → ℕ}
variable (T : (i : ℕ) → Signature K (A i)) (F : FixedField K d)
variable {Q B : Type} {eq : Encoding Q Bool} {eb : Encoding B Bool} {g : Q → B}

private def controlled
    (base : LengthControlledOracleReduction (RawClosedNetwork.validatedEncoding s 1 A) F.encoding eq eb
      ((GeneralFieldReduction.targetTables F (FactorSaturation.PrefixMachine.family (s:=s) T 0)).evaluate F) g)
    {n : ℕ} {H : (i : Fin n) → Signature K (A i.val)}
    (C : RecursiveMachine.Chain (FactorSaturation.PrefixMachine.family (s:=s) T 0) H) :
    LengthControlledOracleReduction (RawClosedNetwork.validatedEncoding n 1 A) F.encoding eq eb
      ((GeneralFieldReduction.targetTables F H).evaluate F) g :=
  match C with
  | .nil => base
  | .snoc previous f power => (RecursiveMachine.step F f power).composeControlled (controlled base previous)

private theorem reduction_eq
    (base : LengthControlledOracleReduction (RawClosedNetwork.validatedEncoding s 1 A) F.encoding eq eb
      ((GeneralFieldReduction.targetTables F (FactorSaturation.PrefixMachine.family (s:=s) T 0)).evaluate F) g)
    {n : ℕ} {H : (i : Fin n) → Signature K (A i.val)}
    (C : RecursiveMachine.Chain (FactorSaturation.PrefixMachine.family (s:=s) T 0) H) :
    (controlled T F base C).reduction=FactorSaturation.PrefixMachine.withTerminal T F base.reduction C := by
  induction C with
  | nil => rfl
  | snoc previous f power ih =>
    change (RecursiveMachine.step F f power).compose (controlled T F base previous).reduction=
      (RecursiveMachine.step F f power).compose (FactorSaturation.PrefixMachine.withTerminal T F base.reduction previous)
    rw [ih]

end Interpreter

namespace SourceV2
variable {s : ℕ} {a : ℕ → ℕ}
variable {L : Type} [Field L] [NumberField L]
variable (φ : L →ₐ[ℚ] AlgebraicComplex) (H : (i : Fin s) → Signature L (a i.val))
variable (j : Fin s) {q : Signature AlgebraicComplex 4}
variable (hj : (⟨a j.val,(OriginalLCodec.mapped φ H) j⟩ : AnySignature AlgebraicComplex)=⟨4,q⟩)
variable (P : QuaternaryEqualityTerminal.PureStep q)

/-- The same original-L one-Delta problem and original-G answer codec.
This is a new explicitly controlled program, not old singleDeltaL by rfl. -/
def singleDelta : LengthControlledOracleReduction (inputEncoding s a)
    (OriginalLCodec.presentation (L:=L)).encoding (RawClosedNetwork.validatedEncoding s 1 a)
    (OriginalLCodec.presentation (L:=L)).encoding
    (BinaryFamily.value H BinaryTable.delta) (OriginalLCodec.value H) := by
  have hn : ∀i b c,(OriginalLCodec.presentation (L:=L)).decode
      ((OriginalLCodec.tables H).edge i b c)=Signature.disequality b c := by
    intro i b c
    simp [OriginalLCodec.tables,GeneralFieldReduction.targetTables,
      Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.FieldReduction.targetTables]
  apply Base.transfer (Base.source (OriginalLCodec.presentation (L:=L)) (OriginalLCodec.tables H) hn)
    (BinaryFamily.value H BinaryTable.delta)
  intro r
  have hv : ValueJoins.signatures (OriginalLCodec.presentation (L:=L)) (OriginalLCodec.tables H)=H := by
    funext i x
    simp [ValueJoins.signatures,OriginalLCodec.tables,GeneralFieldReduction.targetTables,
      Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.FieldReduction.targetTables]
  rw [hv]

def terminal : LengthControlledOracleReduction (QuaternaryUnaryAccess.encoding s a 0)
    (QuaternaryUnaryAccess.F (OriginalLCodec.mapped φ H)).encoding
    (RawClosedNetwork.validatedEncoding s 1 a) (OriginalLCodec.presentation (L:=L)).encoding
    (QuaternaryUnaryAccess.value (OriginalLCodec.mapped φ H) 0) (OriginalLCodec.value H) :=
  (QuaternaryUnaryAccess.toSquare (OriginalLCodec.mapped φ H)).composeControlled
    ((QuaternaryUnaryAccess.squareControlledL φ H j hj P).composeControlled (singleDelta H))

def factors : LengthControlledOracleReduction (QuaternaryUnaryAccess.encoding s a 2)
    (QuaternaryUnaryAccess.F (OriginalLCodec.mapped φ H)).encoding
    (RawClosedNetwork.validatedEncoding s 1 a) (OriginalLCodec.presentation (L:=L)).encoding
    (QuaternaryUnaryAccess.value (OriginalLCodec.mapped φ H) 2) (OriginalLCodec.value H) :=
  Interpreter.controlled (QuaternaryUnaryAccess.table (OriginalLCodec.mapped φ H))
    (QuaternaryUnaryAccess.F (OriginalLCodec.mapped φ H)) (terminal φ H j hj P)
    (QuaternaryUnaryAccess.chain (OriginalLCodec.mapped φ H) j hj P)

/-- UNIQUE V2 source. Caller supplies only original family/field data and the
actual pure event j/hj/P. Every controlled base, physical macro and query bound
is produced internally; the original two-pin chain and ordered ports are reused.
-/
def source : LengthControlledOracleReduction (QuaternaryUnaryAccess.paletteEncoding s a)
    (QuaternaryUnaryAccess.F (OriginalLCodec.mapped φ H)).encoding
    (RawClosedNetwork.validatedEncoding s 1 a) (OriginalLCodec.presentation (L:=L)).encoding
    (QuaternaryUnaryAccess.paletteValue (OriginalLCodec.mapped φ H)) (OriginalLCodec.value H) :=
  (QuaternaryUnaryAccess.paletteControlled (OriginalLCodec.mapped φ H)).composeControlled (factors φ H j hj P)

theorem same_chain : (factors φ H j hj P).reduction=
    FactorSaturation.PrefixMachine.withTerminal (QuaternaryUnaryAccess.table (OriginalLCodec.mapped φ H))
      (QuaternaryUnaryAccess.F (OriginalLCodec.mapped φ H)) (terminal φ H j hj P).reduction
      (QuaternaryUnaryAccess.chain (OriginalLCodec.mapped φ H) j hj P) :=
  Interpreter.reduction_eq _ _ _ _

/- Keep the already constructed factor programme opaque while checking the
outer inliner identities. Unfolding its entire fixed machine is unnecessary
for these identities and duplicates its large finite-state representation. -/
attribute [local irreducible] singleDelta terminal factors

theorem machine : (source φ H j hj P).reduction.machine=
    OracleCompose.machine (factors φ H j hj P).reduction.machine
      (QuaternaryUnaryAccess.paletteControlled (OriginalLCodec.mapped φ H)).reduction.machine :=
  controlled_machine (QuaternaryUnaryAccess.paletteControlled (OriginalLCodec.mapped φ H))
    (factors φ H j hj P)

theorem queryBound : (source φ H j hj P).queryBound=
    (factors φ H j hj P).queryBound.comp
      (QuaternaryUnaryAccess.paletteControlled (OriginalLCodec.mapped φ H)).queryBound := rfl

theorem query_origin (oracle : List Bool → List Bool)
    (ho : RepresentsOracle (RawClosedNetwork.validatedEncoding s 1 a)
      (OriginalLCodec.presentation (L:=L)).encoding (OriginalLCodec.value H) oracle)
    (r : ExactSignatureTables.Input (s+2) 1 (QuaternaryUnaryAccess.paletteArity s a)) (t : ℕ)
    (c : (source φ H j hj P).reduction.machine.Cfg)
    (hr : (source φ H j hj P).reduction.machine.run oracle
      ((QuaternaryUnaryAccess.paletteEncoding s a).encode r) t=some c)
    (hq : (source φ H j hj P).reduction.machine.IsQuery c) :
    LengthControlledOracleReduction.CompositionQueryOrigin
      (QuaternaryUnaryAccess.paletteControlled (OriginalLCodec.mapped φ H)) (factors φ H j hj P) oracle r
      (cast (congrArg (fun M : OracleMachine => M.Cfg) (machine φ H j hj P)) c) :=
  query_origin_of_machine
    (QuaternaryUnaryAccess.paletteControlled (OriginalLCodec.mapped φ H))
    (factors φ H j hj P) (source φ H j hj P).reduction.machine (machine φ H j hj P)
    oracle ho r t c hr hq

theorem safe_query (oracle : List Bool → List Bool)
    (ho : RepresentsOracle (RawClosedNetwork.validatedEncoding s 1 a)
      (OriginalLCodec.presentation (L:=L)).encoding (OriginalLCodec.value H) oracle)
    (r : ExactSignatureTables.Input (s+2) 1 (QuaternaryUnaryAccess.paletteArity s a)) (t : ℕ)
    (c : (source φ H j hj P).reduction.machine.Cfg)
    (hr : (source φ H j hj P).reduction.machine.run oracle
      ((QuaternaryUnaryAccess.paletteEncoding s a).encode r) t=some c)
    (hq : (source φ H j hj P).reduction.machine.IsQuery c) :
    ∃ original : ExactSignatureTables.Input s 1 a,
      c.stk (source φ H j hj P).reduction.machine.queryStack=
        (RawClosedNetwork.validatedEncoding s 1 a).encode original ∧
      (c.stk (source φ H j hj P).reduction.machine.queryStack).length≤
        (source φ H j hj P).queryBound.eval ((QuaternaryUnaryAccess.paletteEncoding s a).encode r).length :=
  (source φ H j hj P).safeQuery oracle ho r t c hr hq

theorem answer_length (oracle : List Bool → List Bool)
    (ho : RepresentsOracle (RawClosedNetwork.validatedEncoding s 1 a)
      (OriginalLCodec.presentation (L:=L)).encoding (OriginalLCodec.value H) oracle)
    (r : ExactSignatureTables.Input (s+2) 1 (QuaternaryUnaryAccess.paletteArity s a)) (t : ℕ)
    (c : (source φ H j hj P).reduction.machine.Cfg)
    (hr : (source φ H j hj P).reduction.machine.run oracle
      ((QuaternaryUnaryAccess.paletteEncoding s a).encode r) t=some c)
    (hq : (source φ H j hj P).reduction.machine.IsQuery c) :
    (oracle (c.stk (source φ H j hj P).reduction.machine.queryStack)).length≤
      ((source φ H j hj P).targetOutput.bound.comp (source φ H j hj P).queryBound).eval
        ((QuaternaryUnaryAccess.paletteEncoding s a).encode r).length :=
  (source φ H j hj P).answer_length_le oracle ho r t c hr hq

theorem target_output_length (r : ExactSignatureTables.Input s 1 a) :
    ((OriginalLCodec.presentation (L:=L)).encoding.encode (OriginalLCodec.value H r)).length≤
      (source φ H j hj P).targetOutput.bound.eval
        ((RawClosedNetwork.validatedEncoding s 1 a).encode r).length :=
  (source φ H j hj P).targetOutput.length_le r

theorem source_output_length
    (r : ExactSignatureTables.Input (s+2) 1 (QuaternaryUnaryAccess.paletteArity s a)) :
    ((QuaternaryUnaryAccess.F (OriginalLCodec.mapped φ H)).encoding.encode
      (QuaternaryUnaryAccess.paletteValue (OriginalLCodec.mapped φ H) r)).length≤
      (source φ H j hj P).sourceOutputPolynomial.eval
        ((QuaternaryUnaryAccess.paletteEncoding s a).encode r).length :=
  (source φ H j hj P).source_output_length_le r

theorem prefix_storage (oracle : List Bool → List Bool)
    (ho : RepresentsOracle (RawClosedNetwork.validatedEncoding s 1 a)
      (OriginalLCodec.presentation (L:=L)).encoding (OriginalLCodec.value H) oracle)
    (r : ExactSignatureTables.Input (s+2) 1 (QuaternaryUnaryAccess.paletteArity s a)) (t : ℕ)
    (c : (source φ H j hj P).reduction.machine.Cfg)
    (hr : (source φ H j hj P).reduction.machine.run oracle
      ((QuaternaryUnaryAccess.paletteEncoding s a).encode r) t=some c) :
    Holant.Complexity.stackSize c.stk≤((QuaternaryUnaryAccess.paletteEncoding s a).encode r).length+
      t*((source φ H j hj P).reduction.machine.primitiveBudget+
        ((source φ H j hj P).targetOutput.bound.comp (source φ H j hj P).queryBound).eval
          ((QuaternaryUnaryAccess.paletteEncoding s a).encode r).length) :=
  (source φ H j hj P).run_stackSize_le oracle ho r t c hr

/-- Full original palette evaluation over the original-G oracle. The time is
the actual V2 inliner time; every ordinary instruction and oracle call is
charged by its actual finite program. No clock/height is caller-supplied. -/
theorem execution (oracle : List Bool → List Bool)
    (ho : RepresentsOracle (RawClosedNetwork.validatedEncoding s 1 a)
      (OriginalLCodec.presentation (L:=L)).encoding (OriginalLCodec.value H) oracle)
    (r : ExactSignatureTables.Input (s+2) 1 (QuaternaryUnaryAccess.paletteArity s a)) :
    ∃ ticks≤(source φ H j hj P).reduction.time.eval
      ((QuaternaryUnaryAccess.paletteEncoding s a).encode r).length,
      (source φ H j hj P).reduction.machine.run oracle
        ((QuaternaryUnaryAccess.paletteEncoding s a).encode r) ticks=
        some ((source φ H j hj P).reduction.machine.output
          ((QuaternaryUnaryAccess.F (OriginalLCodec.mapped φ H)).encoding.encode
            (QuaternaryUnaryAccess.paletteValue (OriginalLCodec.mapped φ H) r))) ∧
      primitiveCount (source φ H j hj P).reduction.machine oracle
        ((source φ H j hj P).reduction.machine.init ((QuaternaryUnaryAccess.paletteEncoding s a).encode r)) ticks≤
        (source φ H j hj P).reduction.machine.primitiveBudget*
          (source φ H j hj P).reduction.time.eval ((QuaternaryUnaryAccess.paletteEncoding s a).encode r).length := by
  let actual := (source φ H j hj P).reduction.correct oracle ho r
  refine ⟨actual.steps,actual.steps_le_m,actual.evals_in_steps,?_⟩
  exact (primitiveCount_le _ _ _ _).trans
    (Nat.mul_le_mul_left _ actual.steps_le_m)

end SourceV2
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableHigherCurrentUnaryQueryControl
