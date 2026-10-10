import Holant.Proofs.Hardness.EOBinaryPlaneFullSupportField
import Holant.Proofs.Algorithms.CBStandardNativeHardness
import Holant.Proofs.Counting.Hardness

/-! Closed natural/conventional counting source for all three nontractable
full-support opposite-pair EO planes. Every field, candidate, Gram graph,
conjugate interpolation loop and original-port compiler is derived internally
from original M, algebraicity, support and literal EOTract failure. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneFullSupportSource
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity Computability
namespace D
export EOBinaryPlaneFullSupportData (ExactlyFour algebraic signature signature_algebraic portSource)
export ComplexPlaneThreeSupportData (Plane)
end D
namespace F
export EOBinaryPlaneFullSupportField
  (field common binary into ambient ambient_star binary_full presentation commonPresentation target_value obstructions)
end F
namespace K
export EOBinaryPlaneFullSupportKernelSource (source)
end K
namespace O
export Holant.LocalDrafts.Hardness.EightVertexNonexception.Source
  (field presentation targetEncoding targetValue)
end O
namespace C
export Holant.LocalDrafts.RemoteWork.PlatonicExits.PhysicalCost (composeControlled)
end C
namespace Standard
export Holant.LocalDrafts.MainChain.CBStandardNativeHardness.Standard (Model injectedEncoding standard_to_witness)
end Standard
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false
variable (M : Signature ℂ 4) (halg : ∀x,IsAlgebraic ℚ (M x))
variable (hp : D.Plane M) (he : DenseEOUnitLocal.EOSupport M) (hf : D.ExactlyFour M)
variable (hn : ¬EOTract {⟨4,D.algebraic M halg⟩})
local instance fieldAlgebra : Algebra ℚ (F.field M hp) := (F.field M hp).algebra'
local instance commonAlgebra : Algebra ℚ (F.common M hp) := (F.common M hp).algebra'
local instance originalAlgebra : Algebra ℚ (O.field M) := (O.field M).algebra'
variable {α : Type} {ea : Encoding α Bool} {count : α→ℕ}

def normalizedSource (w : SharpPWitness ea count) : LengthControlledOracleReduction ea encodingNatBool
    O.targetEncoding (F.presentation M hp halg).encoding count
      (O.targetValue (D.signature M hp) (D.signature_algebraic M hp halg)) := by
  have h := F.obstructions M hp he hf halg hn
  let r := K.source (F.presentation M hp halg) (F.commonPresentation M hp halg)
    (F.into M hp) (F.ambient M hp) (F.ambient_star M hp) (F.binary M hp)
    (F.binary_full M hp he hf) h.1 h.2 w
  have ht : RealDenseSignTwistStageAccess.value (EOBinaryPlaneCore.lift (F.binary M hp))=
      O.targetValue (D.signature M hp) (D.signature_algebraic M hp halg) :=
    funext (F.target_value M hp he halg)
  rw [ht] at r
  exact r

/-- Final original-M oracle and its unchanged generated coefficient codec. -/
def source (w : SharpPWitness ea count) : LengthControlledOracleReduction ea encodingNatBool
    O.targetEncoding (O.presentation M halg).encoding count (O.targetValue M halg) :=
  C.composeControlled (normalizedSource M halg hp he hf hn w) (D.portSource M hp halg)

include hp he hf hn in
theorem witnessCountingHard : Holant.LocalDrafts.CountingHardness.WitnessCountingHard
    O.targetEncoding (O.presentation M halg).encoding (O.targetValue M halg) := by
  intro α ea count w
  exact ⟨(source M halg hp he hf hn w).reduction⟩

variable {Δ T : Type} [Fintype Δ] [Fintype T]
variable (m : Standard.Model Δ T) (input : Bool→Δ) (hinj : Function.Injective input)
variable (clock : Polynomial ℕ) (htime : m.PolyTimeOn input clock)

def standardSource : LengthControlledOracleReduction ea encodingNatBool
    O.targetEncoding (O.presentation M halg).encoding
    (m.physicalCount (Standard.injectedEncoding ea input hinj)) (O.targetValue M halg) :=
  source M halg hp he hf hn (Standard.standard_to_witness (ea:=ea) m input hinj clock htime)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneFullSupportSource
