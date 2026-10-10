import Holant.Proofs.Hardness.ComplexNonselfdualData
import Holant.Proofs.Hardness.ComplexSelfdualSource

/-! Counting hardness for every algebraic complex dense EO
signature. The literal finite four-copy normalization, selfdual source, generated-field
answer map, and actual graph stage are internal. The final oracle is exactly
the original input signature with its own coefficient-field presentation. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.ComplexNonselfdualSource
open Computability Holant Holant.Algebraic Holant.Complexity
namespace D
export ComplexNonselfdualData (generated output output_applicable stageSource)
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
variable (M : Signature ℂ 4) (halg : ∀x,IsAlgebraic ℚ (M x)) (he : DenseEOUnitLocal.EOSupport M) (hm : DenseEOUnitLocal.NonzeroMiddle M)
local instance originalAlgebra : Algebra ℚ (O.field M) := (O.field M).algebra'
local instance generatedAlgebra : Algebra ℚ (O.field (D.output M)) :=
  (O.field (D.output M)).algebra'
variable {α : Type} {ea : Encoding α Bool} {f : α→ℕ}

/-- No spectral branch, cap, torsion order, target clock, or backend is supplied. -/
def source (w : SharpPWitness ea f) : LengthControlledOracleReduction ea encodingNatBool
    O.targetEncoding (O.presentation M halg).encoding f (O.targetValue M halg) :=
  Compose.composeControlled
    (Compose.composeControlled
      (ComplexSelfdualSource.source (D.output M) (F.algebraic M halg (D.generated M))
        (D.output_applicable M hm) w)
      (F.source M halg (D.generated M)))
    (D.stageSource M halg he)

include he hm in
theorem witnessCountingHard : Holant.LocalDrafts.CountingHardness.WitnessCountingHard
    O.targetEncoding (O.presentation M halg).encoding (O.targetValue M halg) := by
  intro α ea f w
  exact ⟨(source M halg he hm w).reduction⟩

attribute [local irreducible] source

def outputs (w : SharpPWitness ea f) (oracle : List Bool→List Bool)
    (ho : RepresentsOracle O.targetEncoding (O.presentation M halg).encoding (O.targetValue M halg) oracle)
    (x : α) : (source M halg he hm w).reduction.machine.OutputsInTime oracle (ea.encode x)
      (encodingNatBool.encode (f x)) ((source M halg he hm w).reduction.time.eval (ea.encode x).length) :=
  (source M halg he hm w).reduction.correct oracle ho x

variable {Δ Q : Type} [Fintype Δ] [Fintype Q]
variable (m : Standard.Model Δ Q) (input : Bool→Δ) (hinj : Function.Injective input)
variable (clock : Polynomial ℕ) (htime : m.PolyTimeOn input clock)

/-- Conventional physical accepting paths with only a source-machine clock. -/
def standardSource : LengthControlledOracleReduction ea encodingNatBool
    O.targetEncoding (O.presentation M halg).encoding
    (m.physicalCount (Standard.injectedEncoding ea input hinj)) (O.targetValue M halg) :=
  source M halg he hm (Standard.standard_to_witness (ea:=ea) m input hinj clock htime)

attribute [local irreducible] standardSource

def standard_outputs (oracle : List Bool→List Bool)
    (ho : RepresentsOracle O.targetEncoding (O.presentation M halg).encoding (O.targetValue M halg) oracle)
    (x : α) :
    (standardSource (ea:=ea) M halg he hm m input hinj clock htime).reduction.machine.OutputsInTime
      oracle (ea.encode x)
      (encodingNatBool.encode (m.physicalCount (Standard.injectedEncoding ea input hinj) x))
      ((standardSource (ea:=ea) M halg he hm m input hinj clock htime).reduction.time.eval (ea.encode x).length) :=
  (standardSource (ea:=ea) M halg he hm m input hinj clock htime).reduction.correct oracle ho x

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.ComplexNonselfdualSource
