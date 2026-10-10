import Holant.Proofs.Hardness.EightVertexCapData
import Holant.Proofs.Hardness.EightVertexCancellationSource

/-! Original-M counting hardness for a complementary cap-weighted eight-vertex
region. A finite original cap is selected from literal coefficients, attached
physically, and fed into the accepted cancellation source. All final graph
queries use only original M/native X and the original answer field/codec. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EightVertexCapSource
open Computability Holant Holant.Algebraic Holant.Complexity
namespace N
export EightVertexCapLocal (Applicable selected selected_spec)
end N
namespace D
export EightVertexCapData (generated output output_applicable stageSource)
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
variable (M : Signature ℂ 4) (halg : ∀x,IsAlgebraic ℚ (M x)) (h : N.Applicable M)
local instance originalAlgebra : Algebra ℚ (O.field M) := (O.field M).algebra'
local instance generatedAlgebra : Algebra ℚ (O.field (D.output M (N.selected M))) :=
  (O.field (D.output M (N.selected M))).algebra'
variable {α : Type} {ea : Encoding α Bool} {f : α→ℕ}

/-- Only original algebraicity and the finite original-coefficient predicate. -/
def source (w : SharpPWitness ea f) : LengthControlledOracleReduction ea encodingNatBool
    O.targetEncoding (O.presentation M halg).encoding f (O.targetValue M halg) :=
  Compose.composeControlled
    (Compose.composeControlled
      (EightVertexCancellationSource.source (D.output M (N.selected M))
        (F.algebraic M halg (D.generated M (N.selected M)))
        (D.output_applicable M (N.selected M) h.1 (N.selected_spec M h)) w)
      (F.source M halg (D.generated M (N.selected M))))
    (D.stageSource M (N.selected M) halg h.1)

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

def standardSource : LengthControlledOracleReduction ea encodingNatBool
    O.targetEncoding (O.presentation M halg).encoding
    (m.physicalCount (Standard.injectedEncoding ea input hinj)) (O.targetValue M halg) :=
  source M halg h (Standard.standard_to_witness (ea:=ea) m input hinj clock htime)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EightVertexCapSource
