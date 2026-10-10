import Holant.Proofs.Dichotomy.Main.PaperTerminalBridgeMacroAccess
import Holant.Proofs.Dichotomy.Retained.StableDenseParityMap
import Holant.Proofs.Hardness.EightVertexCancellationSource
import Holant.Proofs.Hardness.CoefficientEmbedding
import Holant.Proofs.Hardness.SignatureFieldMap
import Holant.Proofs.Closure.ProgrammeCompose

/-! Cancellation hardness reaches any fixed original number-field codec.
The two coefficient-field conversions are actual rational-matrix programmes;
no equality of generated fields or independently chosen encodings is used. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperTerminalBridgeCancellationField
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
namespace O
export Holant.LocalDrafts.Hardness.EightVertexNonexception.Source
  (field presentation tables targetEncoding targetValue TargetInput target_value_exact)
end O
namespace S
export NativeAntiTargetSource (base)
end S
namespace Map
export SignatureFieldMap (mapped mapped_algebraic controlled)
end Map
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type} [Field K] [NumberField K] {degree : ℕ}
local instance : Algebra.IsAlgebraic ℚ K := NumberField.isAlgebraic K
variable (F : FixedField K degree) (M : Signature K 4)

def embedding : K→ₐ[ℚ]ℂ := (algebraicClosure ℚ ℂ).val.comp (CoefficientEmbedding.embedding (L:=K))

theorem algebraic : ∀x,IsAlgebraic ℚ (M x) := fun x=>Algebra.IsAlgebraic.isAlgebraic (M x)

local instance originalAlgebra : Algebra ℚ (O.field M) := (O.field M).algebra'

theorem stored_value (r : O.TargetInput) :
    (O.targetValue M (algebraic M) r:K)=(S.base (fun _ : Fin 1=>M) F).evaluate F r := by
  rw [O.target_value_exact,PaperTerminalBridgeMacroAccess.value]

def coefficient_source : LengthControlledOracleReduction O.targetEncoding
    (O.presentation M (algebraic M)).encoding O.targetEncoding F.encoding
    (O.targetValue M (algebraic M)) ((S.base (fun _ : Fin 1=>M) F).evaluate F) := by
  have source := FieldTransport.fromOriginal (O.presentation M (algebraic M)) F (O.field M).val
    O.targetEncoding (O.targetValue M (algebraic M)) ((O.tables M (algebraic M)).outputBound (O.presentation M (algebraic M)))
  have eq : (fun r=>(O.field M).val (O.targetValue M (algebraic M) r))=
      (S.base (fun _ : Fin 1=>M) F).evaluate F := funext (stored_value F M)
  rw [eq] at source
  exact source

def mapped_source : LengthControlledOracleReduction O.targetEncoding
    (O.presentation (Map.mapped M (embedding (K:=K)))
      (Map.mapped_algebraic M (algebraic M) (embedding (K:=K)))).encoding O.targetEncoding F.encoding
    (O.targetValue (Map.mapped M (embedding (K:=K)))
      (Map.mapped_algebraic M (algebraic M) (embedding (K:=K))))
    ((S.base (fun _ : Fin 1=>M) F).evaluate F) :=
  Programme.compose (Map.controlled M (algebraic M) (embedding (K:=K))) (coefficient_source F M)

variable (applicable : EightVertexCancellationLocal.Applicable M)
variable {α : Type} {ea : Encoding α Bool} {count : α→ℕ}

def source (w : SharpPWitness ea count) : LengthControlledOracleReduction ea encodingNatBool
    O.targetEncoding F.encoding count ((S.base (fun _ : Fin 1=>M) F).evaluate F) :=
  Programme.compose
    (EightVertexCancellationSource.source (Map.mapped M (embedding (K:=K)))
      (Map.mapped_algebraic M (algebraic M) (embedding (K:=K)))
      (StableDenseParityMap.cancellation (embedding (K:=K)).toRingHom M applicable) w)
    (mapped_source F M)

include applicable in
theorem countingHard : Holant.LocalDrafts.CountingHardness.WitnessCountingHard O.targetEncoding F.encoding
    ((S.base (fun _ : Fin 1=>M) F).evaluate F) := by
  intro α ea count w
  exact ⟨(source F M applicable w).reduction⟩

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperTerminalBridgeCancellationField
end
