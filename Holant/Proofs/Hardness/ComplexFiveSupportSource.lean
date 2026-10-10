import Holant.Proofs.Hardness.ComplexFiveSupportData
import Holant.Proofs.Hardness.ComplexNonselfdualSource

/-! Counting hardness for every algebraic complex exactly-five-supported EO
signature. The literal one/two/four-copy construction, cancellation or dense source, generated-field
answer map, and actual graph stage are internal. The final oracle is exactly
the original input signature with its own coefficient-field presentation. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.ComplexFiveSupportSource
open Computability Holant Holant.Algebraic Holant.Complexity
namespace D
export ComplexFiveSupportData (generated output output_eo first_applicable last_middle stageSource)
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
variable (M : Signature ℂ 4) (halg : ∀x,IsAlgebraic ℚ (M x)) (he : DenseEOUnitLocal.EOSupport M) (hm : FiveSupportEOOrdering.ExactlyFive M)
local instance originalAlgebra : Algebra ℚ (O.field M) := (O.field M).algebra'
local instance generatedAlgebra (k : Fin 3) : Algebra ℚ (O.field (D.output M k)) :=
  (O.field (D.output M k)).algebra'
variable {α : Type} {ea : Encoding α Bool} {f : α→ℕ}

/-- No spectral branch, cap, torsion order, target clock, or backend is supplied. -/
def source (w : SharpPWitness ea f) : LengthControlledOracleReduction ea encodingNatBool
    O.targetEncoding (O.presentation M halg).encoding f (O.targetValue M halg) := by
  classical
  by_cases h : ComplexFiveSupportLocal.beta M^2+ComplexFiveSupportLocal.gamma M^2=0
  · exact Compose.composeControlled
      (Compose.composeControlled
        (GeneralGeometricCapSource.source (D.output M 1) (F.algebraic M halg (D.generated M 1))
          (D.first_applicable M he hm h) w)
        (F.source M halg (D.generated M 1)))
      (D.stageSource M he halg 1)
  · exact Compose.composeControlled
      (Compose.composeControlled
        (ComplexNonselfdualSource.source (D.output M 2) (F.algebraic M halg (D.generated M 2))
          (D.output_eo M he 2) (D.last_middle M hm h) w)
        (F.source M halg (D.generated M 2)))
      (D.stageSource M he halg 2)

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

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.ComplexFiveSupportSource
