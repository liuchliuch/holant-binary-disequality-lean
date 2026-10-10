import Holant.Proofs.Hardness.DenseEOUnitCompiler
import Holant.Proofs.Reductions.EightVertexNonexception.Source

/-!
# Dense EO source with its exact paired-pin target

Original algebraic q generates the fixed field/presentation internally. The
full native ONE/TWO graph problem reduces to the literal two-label palette
[original q,01] over that same field. The extra binary label remains explicit;
this is not a pinfree original-q hardness claim. Self-dual q such as EXACT2_4
preclude a general local oriented-pin realization, so that final step is open.
-/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.DenseEOPairedSource
open Computability Holant Holant.Algebraic Holant.Complexity
open DenseEOUnitLocal
namespace Original
export Holant.LocalDrafts.Hardness.EightVertexNonexception.Source
  (field fieldSignature fieldSignature_eq_zero presentation)
end Original
variable {L : Type} [Field L] [Algebra ℚ L]
variable (q : Signature L 4) (halg : ∀x,IsAlgebraic ℚ (q x))
local instance fieldAlgebra : Algebra ℚ (Original.field q) := (Original.field q).algebra'
abbrev presentation := Original.presentation q halg
abbrev targetEncoding := DenseEOUnitCompiler.targetEncoding
abbrev value := DenseEOUnitCompiler.targetValue (presentation q halg) (Original.fieldSignature q)

theorem field_eo (hq : EOSupport q) : EOSupport (Original.fieldSignature q) :=
  fun x hx=>(Original.fieldSignature_eq_zero q x).mpr (hq x hx)

theorem field_middle (hn : NonzeroMiddle q) : NonzeroMiddle (Original.fieldSignature q) := by
  simpa only [NonzeroMiddle,Holant.LocalDrafts.Hardness.EightVertexNonexception.entries,ne_eq,
    Original.fieldSignature_eq_zero] using hn

variable (hq : EOSupport q) (hn : NonzeroMiddle q)

def source : LengthControlledOracleReduction SparseUnitValue.encoding (presentation q halg).encoding
    targetEncoding (presentation q halg).encoding
    (SparseUnitValue.value (K:=Original.field q)) (value q halg) :=
  DenseEOUnitCompiler.controlled (presentation q halg) (Original.fieldSignature q)
    (field_eo q hq) (field_middle q hn)

def outputs (oracle : List Bool → List Bool)
    (ho : RepresentsOracle targetEncoding (presentation q halg).encoding (value q halg) oracle)
    (r : SparseUnitValue.Input) : (source q halg hq hn).reduction.machine.OutputsInTime oracle
      (SparseUnitValue.encoding.encode r) ((presentation q halg).encoding.encode (SparseUnitValue.value r))
      ((source q halg hq hn).reduction.time.eval (SparseUnitValue.encoding.encode r).length) :=
  (source q halg hq hn).reduction.correct oracle ho r

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.DenseEOPairedSource
