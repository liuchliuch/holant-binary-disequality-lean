import Holant.Proofs.Hardness.ThreeModeOriginalSource
import Holant.Proofs.Algorithms.CBStandardNativeHardness
import Holant.Proofs.Counting.Hardness

/-! Conventional physical accepting-path counting into the same original-M
oracle for the explicit norm-dominant, nonzero self-dual three-coefficient EO
subcase. The true annihilator programme, original coefficient field, query
bytes and output normalization are constructed by the imported source. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.ThreeModeCountingSource
open Computability Holant Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain
namespace P
export ThreeModeOriginalSource (source)
end P
namespace O
export Holant.LocalDrafts.Hardness.EightVertexNonexception.Source
  (field presentation targetEncoding targetValue)
end O
namespace Compose
export Holant.LocalDrafts.RemoteWork.PlatonicExits.PhysicalCost (composeControlled)
end Compose
namespace Standard
export CBStandardNativeHardness.Standard (Model injectedEncoding)
end Standard
set_option backward.isDefEq.respectTransparency false
variable {L : Type} [NormedField L] [Algebra ℚ L]
variable (M : Signature L 4) (halg : ∀x,IsAlgebraic ℚ (M x)) (h : ThreeModeOriginalData.Applicable M)
local instance fieldAlgebra : Algebra ℚ (O.field M) := (O.field M).algebra'
variable {α : Type} {ea : Encoding α Bool} {f : α→ℕ}

def source (w : SharpPWitness ea f) :
    LengthControlledOracleReduction ea encodingNatBool O.targetEncoding (O.presentation M halg).encoding
      f (O.targetValue M halg) :=
  Compose.composeControlled (CBSpecializedNativeHardness.source (O.presentation M halg) w)
    (P.source M halg h)

include h in
theorem witnessCountingHard : Holant.LocalDrafts.CountingHardness.WitnessCountingHard
    O.targetEncoding (O.presentation M halg).encoding (O.targetValue M halg) := by
  intro α ea f w
  exact ⟨(source M halg h w).reduction⟩

variable {Δ Q : Type} [Fintype Δ] [Fintype Q]
variable (m : Standard.Model Δ Q) (input : Bool→Δ) (hinj : Function.Injective input)
variable (clock : Polynomial ℕ) (htime : m.PolyTimeOn input clock)

/-- The independent source machine's actual accepting paths, exact original
source input bytes, and its own input-only clock are the only counting inputs. -/
def standardSource : LengthControlledOracleReduction ea encodingNatBool
    O.targetEncoding (O.presentation M halg).encoding
    (m.physicalCount (Standard.injectedEncoding ea input hinj)) (O.targetValue M halg) :=
  Compose.composeControlled
    (CBStandardNativeHardness.source (ea:=ea) m input hinj clock htime (O.presentation M halg))
    (P.source M halg h)

attribute [local irreducible] source standardSource

def standard_outputs (oracle : List Bool→List Bool)
    (ho : RepresentsOracle O.targetEncoding (O.presentation M halg).encoding (O.targetValue M halg) oracle)
    (x : α) :
    (standardSource (ea:=ea) M halg h m input hinj clock htime).reduction.machine.OutputsInTime
      oracle (ea.encode x)
      (encodingNatBool.encode (m.physicalCount (Standard.injectedEncoding ea input hinj) x))
      ((standardSource (ea:=ea) M halg h m input hinj clock htime).reduction.time.eval (ea.encode x).length) :=
  (standardSource (ea:=ea) M halg h m input hinj clock htime).reduction.correct oracle ho x

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.ThreeModeCountingSource
