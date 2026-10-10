import Holant.Proofs.Reductions.EightVertexNonexception.SixVertexInterpolation.VerifierGates.GlobalSignedMatching.Source
import Holant.Proofs.Reductions.EightVertexNonexception.SixVertexInterpolation.VerifierGates.NativeCubicMatching.OriginalFieldMap
import Holant.Proofs.Algorithms.FieldCodec
import Holant.Proofs.Algorithms.ControlledReduction
import Holant.Proofs.Tractability.ControlledComposition


namespace Holant.LocalDrafts.MainChain.NativeMatchingOriginalFieldSource
open Turing Computability Holant Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing
open Holant.LocalDrafts.Hardness.EightVertexNonexception.SixVertexInterpolation.VerifierGates
open Holant.LocalDrafts.MainChain
noncomputable section

namespace Matching
export WeightedMatchingInterpolation (UnitInput unitEncoding unitValue)
end Matching
namespace Native
export NativeCubicMatching.OriginalFieldMap
  (TargetInput targetEncoding targetValue unitValueL top)
end Native
abbrev Circuit := Holant.LocalDrafts.CountingHardness.CircuitInstance
namespace Circuit
export Holant.LocalDrafts.CountingHardness.CircuitInstance (encoding value)
end Circuit
abbrev rationalField := NativeCubicMatching.Source.F

variable {L : Type} [Field L] [Algebra ℚ L] {d : ℕ}
variable (F : FixedField L d)

def embedding : ℚ →ₐ[ℚ] L := Algebra.ofId ℚ L
def forward := FieldCodec.computes rationalField F (embedding (L:=L)).toLinearMap
def backward := FieldCodec.retractComputes rationalField F (embedding (L:=L))

/-- The image promise is derived for the real intermediate matching value.
The program is the total fixed matrix map, not a rationality-test oracle. -/
theorem recovered (g : Matching.UnitInput) :
    (embedding (L:=L)).toLinearMap.leftInverse (Native.unitValueL g)=Matching.unitValue g := by
  simpa only [NativeCubicMatching.OriginalFieldMap.unitValueL,embedding,Algebra.ofId_apply] using
    FieldCodec.retract_embedding (embedding (L:=L)) (Matching.unitValue g)

/-- The actual original-field answer length follows from the old rational
matching bound and the installed forward basis-conversion program. -/
def unitAnswerOutput : PolynomialOutputBound Matching.unitEncoding F.encoding Native.unitValueL where
  bound := (forward F).outputBound.bound.comp
    (WeightedMatchingInterpolation.Source.targetOutput rationalField).bound
  length_le g := by
    rw [Polynomial.eval_comp]
    have hf := (forward F).outputBound.length_le (Matching.unitValue g)
    have hm := (WeightedMatchingInterpolation.Source.targetOutput rationalField).length_le g
    exact hf.trans (natPolynomial_eval_mono (forward F).outputBound.bound hm)

/-- One real unchanged UnitInput query, followed by the actual F -> Q
answer machine. No oracle convention or encoding is silently substituted. -/
def unitAnswerSource : LengthControlledOracleReduction Matching.unitEncoding rationalField.encoding
    Matching.unitEncoding F.encoding Matching.unitValue Native.unitValueL :=
  controlledOneQueryOfEq (identityComputes Matching.unitEncoding) (backward F)
    (unitAnswerOutput F) Matching.unitValue (fun g => (recovered (L:=L) g).symm)

theorem recovered_answer_bytes (g : Matching.UnitInput) :
    rationalField.encoding.encode ((embedding (L:=L)).toLinearMap.leftInverse (Native.unitValueL g))=
      rationalField.encoding.encode (Matching.unitValue g) :=
  congrArg rationalField.encoding.encode (recovered (L:=L) g)

/-- This receipt is the physical answer recoder on arbitrary original-field
bytes in its typed domain, with its installed polynomial clock. -/
def answerReceipt (y : L) :
    TM2OutputsInTime (backward F).machine.computer (F.encoding.encode y)
      (some (rationalField.encoding.encode ((embedding (L:=L)).toLinearMap.leftInverse y)))
      ((backward F).time.eval (F.encoding.encode y).length) :=
  (backward F).outputs y

/-- The real matching callee's output is retracted only after its own scalar
postprocessor has produced unitValueL; no native weighted tensor is retracted
in place of its corrected value. -/
def unitToNative : LengthControlledOracleReduction Matching.unitEncoding rationalField.encoding
    Native.targetEncoding F.encoding Matching.unitValue Native.targetValue :=
  (unitAnswerSource F).composeControlled (Native.top F)

/-- Sole circuit consumer. The existing signed interpolation and its 2^-m
correction now call the original-field native matching machine through the
actual answer recoder above. Every new query origin and bound comes from the
existing controlled composition producers. -/
def source : LengthControlledOracleReduction Circuit.encoding rationalField.encoding
    Native.targetEncoding F.encoding (fun c => (Circuit.value c : ℚ)) Native.targetValue :=
  GlobalSignedMatching.Source.circuitSource.composeControlled (unitToNative F)

theorem source_queryBound : (source F).queryBound=
    ((Native.top F).queryBound.comp (unitAnswerSource F).queryBound).comp
      GlobalSignedMatching.Source.circuitSource.queryBound := rfl
theorem source_targetOutput : (source F).targetOutput=(Native.top F).targetOutput := rfl

/-- A literal finite-program receipt, internally produced from the original
circuit and a represented original-field native oracle. -/
def outputs (oracle : List Bool → List Bool)
    (ho : RepresentsOracle Native.targetEncoding F.encoding Native.targetValue oracle)
    (c : Circuit) := (source F).reduction.correct oracle ho c

/-- Every query of the full circuit program retains the actual original-field
target language; no arbitrary Poly correctness theorem supplies this fact. -/
theorem query_origin (oracle : List Bool → List Bool)
    (ho : RepresentsOracle Native.targetEncoding F.encoding Native.targetValue oracle)
    (c : Circuit) (t : ℕ) (cfg : (source F).reduction.machine.Cfg)
    (hr : (source F).reduction.machine.run oracle (Circuit.encoding.encode c) t=some cfg)
    (hq : (source F).reduction.machine.IsQuery cfg) :
    ∃ q : Native.TargetInput,
      cfg.stk (source F).reduction.machine.queryStack=Native.targetEncoding.encode q ∧
      (Native.targetEncoding.encode q).length≤(source F).queryBound.eval (Circuit.encoding.encode c).length :=
  by
    obtain ⟨q,hq,hl⟩ := (source F).safeQuery oracle ho c t cfg hr hq
    exact ⟨q,hq,by simpa only [hq] using hl⟩

theorem answer_length (oracle : List Bool → List Bool)
    (ho : RepresentsOracle Native.targetEncoding F.encoding Native.targetValue oracle)
    (c : Circuit) (t : ℕ) (cfg : (source F).reduction.machine.Cfg)
    (hr : (source F).reduction.machine.run oracle (Circuit.encoding.encode c) t=some cfg)
    (hq : (source F).reduction.machine.IsQuery cfg) :
    (oracle (cfg.stk (source F).reduction.machine.queryStack)).length≤
      ((source F).targetOutput.bound.comp (source F).queryBound).eval (Circuit.encoding.encode c).length :=
  (source F).answer_length_le oracle ho c t cfg hr hq

end
end Holant.LocalDrafts.MainChain.NativeMatchingOriginalFieldSource
