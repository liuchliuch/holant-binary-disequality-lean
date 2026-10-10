import Holant.Proofs.Hardness.ComplexPlaneThreeSupportField
import Holant.Proofs.Hardness.BinaryCSPCountingSource
import Holant.Proofs.Hardness.BinaryCSPProgrammeRestricted
import Holant.Proofs.Algorithms.CBStandardNativeHardness
import Holant.Proofs.Platonic.PhysicalCostComposition
import Holant.Proofs.Counting.Hardness

/-! Closed counting sources for every three-supported EO opposite-pair plane.
The original plane/missing-word choices, signed-circuit graph, positive-power
support extraction, native cycle writer, unused-variable multiplier, original
field recoding and natural decoder are constructed internally. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.ComplexPlaneThreeSupportSource
open Computability Holant Holant.Algebraic Holant.Complexity
namespace D
export ComplexPlaneThreeSupportData (Plane ExactlyThree output_algebraic portSource)
end D
namespace F
export ComplexPlaneThreeSupportField
  (signature field fieldSignature kernel presentation weightA weightB weightC weights_nonzero spectrum field_lift support_eq_nand target_value)
end F
namespace P
export BinaryCSPProgrammeValidated (Input inputEncoding)
end P
namespace Signed
export BinaryCSPProgrammeSigned (sourceValue targetValue controlled)
end Signed
namespace Restricted
export BinaryCSPProgrammeRestricted (sourceValue targetValue supportControlled)
end Restricted
namespace Native
export BinaryCSPProgrammeNative (sourceValue targetValue controlled)
end Native
namespace O
export Holant.LocalDrafts.Hardness.EightVertexNonexception.Source
  (field presentation targetEncoding targetValue)
end O
namespace Compose
export Holant.LocalDrafts.RemoteWork.PlatonicExits.PhysicalCost (composeControlled)
end Compose
namespace Standard
export Holant.LocalDrafts.MainChain.CBStandardNativeHardness.Standard (Model injectedEncoding standard_to_witness)
end Standard
set_option backward.isDefEq.respectTransparency false
variable {L : Type} [Field L] [Algebra ℚ L]
variable (M : Signature L 4) (halg : ∀x,IsAlgebraic ℚ (M x))
variable (hp : D.Plane M) (he : DenseEOUnitLocal.EOSupport M) (ht : D.ExactlyThree M)
local instance fieldAlgebra : Algebra ℚ (F.field M hp he ht) := (F.field M hp he ht).algebra'
local instance originalAlgebra : Algebra ℚ (O.field M) := (O.field M).algebra'

/-- The validated support extractor composes with the literal original-field
cycle oracle, with the exact2^unused correction in its actual programme. -/
def unsignedToNormalized : LengthControlledOracleReduction P.inputEncoding
    (F.presentation M hp he ht halg).encoding O.targetEncoding
    (F.presentation M hp he ht halg).encoding
    (Signed.targetValue (K:=F.field M hp he ht))
    (O.targetValue (F.signature M hp he ht) (D.output_algebraic M halg hp he ht)) := by
  let r := Restricted.supportControlled (F.presentation M hp he ht halg)
    (F.weightA M hp he ht) (F.weightB M hp he ht) (F.weightC M hp he ht)
    (F.kernel M hp he ht) (F.weights_nonzero M hp he ht).1
    (F.weights_nonzero M hp he ht).2.1 (F.weights_nonzero M hp he ht).2.2
    (F.spectrum M hp he ht)
  have hs : Restricted.sourceValue (F.kernel M hp he ht)=
      Signed.targetValue (K:=F.field M hp he ht) := by
    funext x
    exact F.support_eq_nand M hp he ht x.val
  rw [hs] at r
  let n := Native.controlled (F.presentation M hp he ht halg) (F.fieldSignature M hp he ht)
    (F.kernel M hp he ht) (F.field_lift M hp he ht)
  have hn : Native.targetValue (F.presentation M hp he ht halg) (F.fieldSignature M hp he ht)=
      O.targetValue (F.signature M hp he ht) (D.output_algebraic M halg hp he ht) :=
    funext (F.target_value M hp he ht halg)
  rw [hn] at n
  exact Compose.composeControlled r n

variable {α : Type} {ea : Encoding α Bool} {f : α→ℕ}

def normalizedSource (w : SharpPWitness ea f) : LengthControlledOracleReduction ea encodingNatBool
    O.targetEncoding (F.presentation M hp he ht halg).encoding f
    (O.targetValue (F.signature M hp he ht) (D.output_algebraic M halg hp he ht)) :=
  Compose.composeControlled
    (Compose.composeControlled (BinaryCSPCountingSource.source (F.presentation M hp he ht halg) w)
      (Signed.controlled (F.presentation M hp he ht halg)))
    (unsignedToNormalized M halg hp he ht)

/-- The final oracle is exactly the original M and its original presentation;
no binary hard basis, cap, target clock, endpoint or decoder is supplied. -/
def source (w : SharpPWitness ea f) : LengthControlledOracleReduction ea encodingNatBool
    O.targetEncoding (O.presentation M halg).encoding f (O.targetValue M halg) :=
  Compose.composeControlled (normalizedSource M halg hp he ht w) (D.portSource M halg hp he ht)

include hp he ht in
theorem witnessCountingHard : Holant.LocalDrafts.CountingHardness.WitnessCountingHard
    O.targetEncoding (O.presentation M halg).encoding (O.targetValue M halg) := by
  intro α ea f w
  exact ⟨(source M halg hp he ht w).reduction⟩

variable {Δ Q : Type} [Fintype Δ] [Fintype Q]
variable (m : Standard.Model Δ Q) (input : Bool→Δ) (hinj : Function.Injective input)
variable (clock : Polynomial ℕ) (htime : m.PolyTimeOn input clock)

def standardSource : LengthControlledOracleReduction ea encodingNatBool
    O.targetEncoding (O.presentation M halg).encoding
    (m.physicalCount (Standard.injectedEncoding ea input hinj)) (O.targetValue M halg) :=
  source M halg hp he ht (Standard.standard_to_witness (ea:=ea) m input hinj clock htime)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.ComplexPlaneThreeSupportSource
