import Holant.Proofs.Reductions.CanonicalFamily.Reduction
import Holant.Proofs.Reductions.CyclicRetainedAugmentation.LiteralCodec


noncomputable section
namespace Holant.LocalDrafts.Hardness.FrozenFactorNormalization.ScalarProgram
open Holant.Tractable
open Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open FixedGadgetSubstitution.Compiler
open UniversalPairReduction.Surgery
open Holant.LocalDrafts.MainChain
open GeneralExtraction
namespace GOT
export GeneralOriginalTarget (coefficients originalField originalPresentation originalValue originalTables target_exact)
end GOT
namespace Relabel
export CanonicalFamily.Relabel (input computes value_scaled ordered_ports)
end Relabel
namespace OP
export RootPreprocessing.OccurrenceProduct (value computes)
end OP
variable {m n : ℕ} {a b : ℕ → ℕ}
variable (G : (i : Fin m) → Signature AlgebraicComplex (a i.val))
variable (H : (i : Fin n) → Signature AlgebraicComplex (b i.val))
variable (σ : Fin m → Fin n) (ha : ∀ i, b (σ i).val = a i.val)
variable (κ : Fin m → AlgebraicComplex)

def extra := FamilyFieldInclusion.combined (GOT.coefficients H) κ
def coefficient := FamilyFieldInclusion.combined (GOT.coefficients G) (extra H κ)
theorem algebraic (i) : IsAlgebraic ℚ (coefficient G H κ i) := Algebra.IsAlgebraic.isAlgebraic _
abbrev field := familyField (coefficient G H κ)
abbrev presentation := familyPresentation (coefficient G H κ) (algebraic G H κ)
def sourceEmbedding : GOT.originalField G →ₐ[ℚ] field G H κ :=
  FamilyFieldInclusion.embedding (GOT.coefficients G) (extra H κ)
theorem target_le : GOT.originalField H ≤ field G H κ := by
  apply IntermediateField.adjoin_le_iff.mpr
  rintro z ⟨j,rfl⟩
  exact coefficient_mem_familyField (coefficient G H κ) (.inr (.inl j))
def targetEmbedding : GOT.originalField H →ₐ[ℚ] field G H κ := IntermediateField.inclusion (target_le G H κ)
def scalar (i : Fin m) : field G H κ := fieldCoefficient (coefficient G H κ) (.inr (.inr i))
def factor (r : ExactSignatureTables.Input m 1 a) : field G H κ := OP.value (scalar G H κ) r.val
def query := Relabel.input σ ha
def queryComputes := Relabel.computes σ ha
def factorComputes : Computes (RawClosedNetwork.validatedEncoding m 1 a)
    (presentation G H κ).encoding (factor G H κ) :=
  OP.computes (presentation G H κ) (scalar G H κ)
def answerComputes : Computes (GOT.originalPresentation H).encoding
    (presentation G H κ).encoding (targetEmbedding G H κ) :=
  FieldCodec.computes (GOT.originalPresentation H) (presentation G H κ)
    (targetEmbedding G H κ).toLinearMap
def retractComputes : Computes (presentation G H κ).encoding
    (GOT.originalPresentation G).encoding (sourceEmbedding G H κ).toLinearMap.leftInverse :=
  FieldCodec.retractComputes (GOT.originalPresentation G) (presentation G H κ) (sourceEmbedding G H κ)

variable (ht : ∀ i : Fin m, ∀ bits,
  Choice.table G i.val bits = κ i * Choice.table H (σ i).val bits)
include ht in
theorem ambient (r : ExactSignatureTables.Input m 1 a) :
    (GOT.originalValue G r : AlgebraicComplex) = OP.value κ r.val *
      (GOT.originalValue H (query σ ha r) : AlgebraicComplex) := by
  rw [GOT.target_exact,GOT.target_exact,Choice.denote_eq_evaluate,Choice.denote_eq_evaluate]
  exact Relabel.value_scaled σ (Choice.table G) (Choice.table H) κ ha r ht
include ht in
theorem field_identity (r : ExactSignatureTables.Input m 1 a) :
    sourceEmbedding G H κ (GOT.originalValue G r) =
      factor G H κ r * targetEmbedding G H κ (GOT.originalValue H (query σ ha r)) := by
  apply Subtype.ext
  change (GOT.originalValue G r : AlgebraicComplex) =
    (factor G H κ r : AlgebraicComplex) * (GOT.originalValue H (query σ ha r) : AlgebraicComplex)
  rw [show (factor G H κ r : AlgebraicComplex) = OP.value κ r.val from
    CanonicalFamily.OP.map (scalar G H κ) (field G H κ).subtype r.val]
  exact ambient G H σ ha κ ht r

def pre (r : ExactSignatureTables.Input m 1 a) := ([query σ ha r],factor G H κ r)
def preComputes : Computes (RawClosedNetwork.validatedEncoding m 1 a)
    (OracleBatch.contextEncoding (RawClosedNetwork.validatedEncoding n 1 b)
      (presentation G H κ).encoding) (pre G H σ ha κ) :=
  pairComputes (fixedListComputes (RawClosedNetwork.validatedEncoding m 1 a)
    (RawClosedNetwork.validatedEncoding n 1 b) (fun r (_ : Unit) => query σ ha r)
    (fun _ => queryComputes σ ha) [()]) (factorComputes G H κ)
def post (p : List (GOT.originalField H) × field G H κ) : GOT.originalField G :=
  (sourceEmbedding G H κ).toLinearMap.leftInverse
    (p.2 * targetEmbedding G H κ (p.1.getD 0 0))
def postComputes : Computes
    (OracleBatch.contextEncoding (GOT.originalPresentation H).encoding (presentation G H κ).encoding)
    (GOT.originalPresentation G).encoding (post G H κ) := by
  let answer := ((Wiring.firstComputes (framedListEncoding (GOT.originalPresentation H).encoding)
    (presentation G H κ).encoding).andThen (getDComputes (GOT.originalPresentation H).encoding 0 0)).andThen
      (answerComputes G H κ)
  let f := Wiring.secondComputes (framedListEncoding (GOT.originalPresentation H).encoding)
    (presentation G H κ).encoding
  exact ((pairComputes f answer).andThen (Concrete.fieldMultiplication (presentation G H κ))).andThen
    (retractComputes G H κ)
include ht in
theorem recovery (r : ExactSignatureTables.Input m 1 a) :
    GOT.originalValue G r = post G H κ (OracleBatch.answers (GOT.originalValue H) (pre G H σ ha κ r)) := by
  change GOT.originalValue G r = (sourceEmbedding G H κ).toLinearMap.leftInverse
    (factor G H κ r * targetEmbedding G H κ (GOT.originalValue H (query σ ha r)))
  rw [←field_identity G H σ ha κ ht r]
  exact (FieldCodec.retract_embedding (sourceEmbedding G H κ) (GOT.originalValue G r)).symm

def reduction : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding m 1 a) (GOT.originalPresentation G).encoding
    (RawClosedNetwork.validatedEncoding n 1 b) (GOT.originalPresentation H).encoding
    (GOT.originalValue G) (GOT.originalValue H) := by
  have he : GOT.originalValue G = fun r =>
      post G H κ (OracleBatch.answers (GOT.originalValue H) (pre G H σ ha κ r)) :=
    funext (recovery G H σ ha κ ht)
  rw [he]
  exact TraceQueryControl.controlledBatch (preComputes G H σ ha κ) (postComputes G H κ)
    ((GOT.originalTables H).outputBound (GOT.originalPresentation H))

theorem ordered_ports (r : ExactSignatureTables.Input m 1 a) :
    (query σ ha r).val.vertices.map Prod.snd = r.val.vertices.map Prod.snd := Relabel.ordered_ports σ r.val
theorem edges (r : ExactSignatureTables.Input m 1 a) :
    (query σ ha r).val.edges = r.val.edges := rfl
theorem query_bound (r : ExactSignatureTables.Input m 1 a) :
    ((RawClosedNetwork.validatedEncoding n 1 b).encode (query σ ha r)).length ≤
      (queryComputes σ ha).outputBound.bound.eval
        (((RawClosedNetwork.validatedEncoding m 1 a).encode r).length) :=
  (queryComputes σ ha).outputBound.length_le r

end Holant.LocalDrafts.Hardness.FrozenFactorNormalization.ScalarProgram
