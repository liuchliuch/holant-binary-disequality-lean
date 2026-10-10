import Holant.Proofs.Hardness.GeneralEOTensorPowerRemovalOriginalTables

/-! Tensor-power removal between the two literal original dictionaries. Both
faithful number-field codecs are constructed from their own coefficients; the
source and target fields are not identified. The finite residue anchors are
fixed nonuniformly with the signatures and exponent, before runtime. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOTensorPowerRemovalOriginalSource
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open UniversalPairReduction.Surgery
namespace F
export GeneralEOTensorPowerRemovalOriginalField
  (sourceFamily targetFamily sourceField targetField embedding old distinguished target)
end F
namespace O
export Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalTarget
  (originalPresentation originalValue)
end O
namespace P
export GeneralEOTensorPowerRemovalPadding (Input inputEncoding value query)
end P
namespace T
export GeneralEOTensorPowerRemovalTables (listValue)
export GeneralEOTensorPowerRemovalOriginalTables (source_value target_coefficient)
end T
namespace R
export GeneralEOTensorPowerRemovalReduction (queryEncoding controlled run_trace exact_calls_and_primitive)
end R
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] GeneralEOTensorPowerRemovalReduction.controlled

/-- Semantic replacement preserves every command, stack and runtime bound. -/
def revalue {α β γ δ : Type} {ea : Encoding α Bool} {eb : Encoding β Bool}
    {ec : Encoding γ Bool} {ed : Encoding δ Bool} {f f' : α→β} {g : γ→δ}
    (r : LengthControlledOracleReduction ea eb ec ed f g) (h : ∀x,f x=f' x) :
    LengthControlledOracleReduction ea eb ec ed f' g where
  reduction := {
    machine := r.reduction.machine
    time := r.reduction.time
    correct := fun oracle ho x => by
      rw [←h x]
      exact r.reduction.correct oracle ho x }
  targetOutput := r.targetOutput
  queryBound := r.queryBound
  safeQuery := r.safeQuery

variable {s n : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
variable (f : Signature AlgebraicComplex n) (k : ℕ) (hk : 0<k)
local instance sourceAlgebra : Algebra ℚ (F.sourceField G f) := (F.sourceField G f).algebra'
local instance targetAlgebra : Algebra ℚ (F.targetField G f k) := (F.targetField G f k).algebra'

abbrev sourcePresentation := O.originalPresentation (F.sourceFamily G f)
abbrev targetPresentation := O.originalPresentation (F.targetFamily G f k)
abbrev sourceValue := O.originalValue (F.sourceFamily G f)
abbrev targetValue := O.originalValue (F.targetFamily G f k)

/-- Actual fixed-signature programme, with the original target answer codec. -/
def programme := R.controlled (sourcePresentation G f) (targetPresentation G f k)
  (F.embedding G f k) (Choice.table (F.old G f)) (T.listValue (F.distinguished G f))
  k hk (F.target G f k) (T.target_coefficient G f k)

/-- The full source-to-target theorem uses original decoded network values on
both sides, not an assumed equality of answer encodings. -/
def source : LengthControlledOracleReduction (P.inputEncoding s n a) (sourcePresentation G f).encoding
    (R.queryEncoding k) (targetPresentation G f k).encoding (sourceValue G f) (targetValue G f k) :=
  revalue (programme G f k hk) (T.source_value G f)

abbrev query (r : P.Input s n a) :=
  P.query (Choice.table (F.old G f)) (T.listValue (F.distinguished G f)) k hk r

/-- Correctness for the actual original-field output word. -/
def outputs (oracle : List Bool→List Bool)
    (ho : RepresentsOracle (R.queryEncoding k) (targetPresentation G f k).encoding (targetValue G f k) oracle)
    (r : P.Input s n a) := (source G f k hk).reduction.correct oracle ho r

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOTensorPowerRemovalOriginalSource
