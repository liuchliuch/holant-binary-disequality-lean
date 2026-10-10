import Holant.Proofs.Hardness.EightVertexCancellationData
import Holant.Proofs.Hardness.ComplexFiveSupportSource

/-! Counting hardness for the literal eight-vertex cancellation region.
The actual two-copy original-M network yields an internally selected five- or
six-supported EO source. Original labels and the original coefficient-field
answer encoding are retained by physical substitution and field retraction.
This is a local branch, not the universal nonexception theorem. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EightVertexCancellationSource
open Computability Holant Holant.Algebraic Holant.Complexity
namespace D
export EightVertexCancellationData (generated output output_eo output_middle_or_five stageSource)
end D
namespace F
export GeneratedSignatureField (algebraic source)
end F
namespace O
export Holant.LocalDrafts.Hardness.EightVertexNonexception.Source
  (field presentation targetEncoding targetValue)
end O
namespace Compose
export Holant.LocalDrafts.RemoteWork.PlatonicExits.PhysicalCost (composeControlled)
end Compose
namespace Standard
export Holant.LocalDrafts.MainChain.CBStandardNativeHardness.Standard
  (Model injectedEncoding standard_to_witness)
end Standard
set_option backward.isDefEq.respectTransparency false
variable (M : Signature ℂ 4) (halg : ∀x,IsAlgebraic ℚ (M x)) (h : EightVertexCancellationLocal.Applicable M)
local instance originalAlgebra : Algebra ℚ (O.field M) := (O.field M).algebra'
local instance generatedAlgebra : Algebra ℚ (O.field (D.output M)) :=
  (O.field (D.output M)).algebra'
variable {α : Type} {ea : Encoding α Bool} {f : α→ℕ}

/-- No spectral branch, cap, torsion order, target clock, or backend is supplied. -/
def source (w : SharpPWitness ea f) : LengthControlledOracleReduction ea encodingNatBool
    O.targetEncoding (O.presentation M halg).encoding f (O.targetValue M halg) := by
  classical
  have base : LengthControlledOracleReduction ea encodingNatBool O.targetEncoding
      (O.presentation (D.output M) (F.algebraic M halg (D.generated M))).encoding
      f (O.targetValue (D.output M) (F.algebraic M halg (D.generated M))) := by
    by_cases hm : DenseEOUnitLocal.NonzeroMiddle (D.output M)
    · exact ComplexNonselfdualSource.source (D.output M)
        (F.algebraic M halg (D.generated M)) (D.output_eo M h) hm w
    · exact ComplexFiveSupportSource.source (D.output M)
        (F.algebraic M halg (D.generated M)) (D.output_eo M h)
        ((D.output_middle_or_five M h).resolve_left hm) w
  exact Compose.composeControlled
    (Compose.composeControlled base (F.source M halg (D.generated M)))
    (D.stageSource M halg h.even)

include h in
theorem witnessCountingHard : Holant.LocalDrafts.CountingHardness.WitnessCountingHard
    O.targetEncoding (O.presentation M halg).encoding (O.targetValue M halg) := by
  intro α ea f w
  exact ⟨(source M halg h w).reduction⟩

attribute [local irreducible] source

def outputs (w : SharpPWitness ea f) (oracle : List Bool→List Bool)
    (ho : RepresentsOracle O.targetEncoding (O.presentation M halg).encoding (O.targetValue M halg) oracle)
    (x : α) : (source M halg h w).reduction.machine.OutputsInTime oracle (ea.encode x)
      (encodingNatBool.encode (f x)) ((source M halg h w).reduction.time.eval (ea.encode x).length) :=
  (source M halg h w).reduction.correct oracle ho x

variable {Δ Q : Type} [Fintype Δ] [Fintype Q]
variable (m : Standard.Model Δ Q) (input : Bool→Δ) (hinj : Function.Injective input)
variable (clock : Polynomial ℕ) (htime : m.PolyTimeOn input clock)

/-- Conventional physical accepting paths with only a source-machine clock. -/
def standardSource : LengthControlledOracleReduction ea encodingNatBool
    O.targetEncoding (O.presentation M halg).encoding
    (m.physicalCount (Standard.injectedEncoding ea input hinj)) (O.targetValue M halg) :=
  source M halg h (Standard.standard_to_witness (ea:=ea) m input hinj clock htime)

attribute [local irreducible] standardSource

def standard_outputs (oracle : List Bool→List Bool)
    (ho : RepresentsOracle O.targetEncoding (O.presentation M halg).encoding (O.targetValue M halg) oracle)
    (x : α) :
    (standardSource (ea:=ea) M halg h m input hinj clock htime).reduction.machine.OutputsInTime
      oracle (ea.encode x)
      (encodingNatBool.encode (m.physicalCount (Standard.injectedEncoding ea input hinj) x))
      ((standardSource (ea:=ea) M halg h m input hinj clock htime).reduction.time.eval (ea.encode x).length) :=
  (standardSource (ea:=ea) M halg h m input hinj clock htime).reduction.correct oracle ho x

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EightVertexCancellationSource
