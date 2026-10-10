import Holant.Proofs.Reductions.GeneralExtraction.GeneralFieldReduction
import Holant.Proofs.Reductions.GeneralExtraction.RightPowerExposure


noncomputable section
namespace Holant.LocalDrafts.Hardness.GeneralExtraction.RetainedPairReduction
open Holant.Algebraic Holant.Complexity FixedGadgetSubstitution
open Holant.LocalDrafts.BinaryInterpolation.SingularExtraction
open GeneralPowerExposure
variable {K : Type} [Field K] [Algebra ℚ K] {d s : ℕ} {arity : ℕ → ℕ}
variable (F : FixedField K d) (G : (i : Fin s) → Signature K (arity i.val))
variable (f : Signature K (arity s)) (g : Signature K (arity (s+1)))

def extended : (i : Fin (s+1)) → Signature K (arity i.val) :=
  Tables.typed (GeneralOriginalQuery.factorTable G f) (s+1) arity

def growLabels {n : ℕ} {S : NetworkShape n} (L : Labelling S s 1 arity) :
    Labelling S (s+1) 1 arity where
  vertex v := ⟨(L.vertex v).val, Nat.lt_trans (L.vertex v).isLt (Nat.lt_succ_self s)⟩
  vertex_arity := L.vertex_arity
  edge := L.edge

def weaken (R : PowerMacro G g) : PowerMacro (extended G f) g where
  exponent := R.exponent
  positive := R.positive
  scale := R.scale
  scale_ne_zero := R.scale_ne_zero
  network := R.network
  labels := growLabels R.labels
  value := by
    rw [Labelling.denote_template]
    have he : ((growLabels R.labels).sourceNetwork (extended G f)
        (fun _ => Signature.disequality)).denote =
        (R.labels.sourceNetwork G (fun _ => Signature.disequality)).denote := by
      apply Network.denote_congr
      · intro v x
        change Tables.typed (GeneralOriginalQuery.factorTable G f) (s+1) arity
          ⟨(R.labels.vertex v).val, _⟩ _ = _
        rw [GeneralOriginalQuery.source_old]
        rfl
      · intro e a b
        rfl
    rw [he, ← Labelling.denote_template]
    exact R.value

variable (P : PowerMacro G f) (R : PowerMacro G g)

def sourceValue := GeneralFieldReduction.sourceValue (extended G f) g

theorem middle_value (r : GeneralOriginalQuery.Input (s:=s) (arity:=arity)) :
    (GeneralFieldReduction.targetTables F (extended G f)).evaluate F r =
      GeneralFieldReduction.sourceValue G f r := by
  rw [FieldReduction.target_evaluate]
  unfold extended
  rw [Tables.denote_eq_evaluate]
  rfl

def outerControlled : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding (s+2) 1 arity) F.encoding
    (RawClosedNetwork.validatedEncoding (s+1) 1 arity) F.encoding
    (sourceValue G f g) (GeneralFieldReduction.sourceValue G f) := by
  have H := GeneralFieldReduction.controlled F (extended G f) g (weaken G f g R)
  have he : (GeneralFieldReduction.targetTables F (extended G f)).evaluate F =
      GeneralFieldReduction.sourceValue G f := funext (middle_value F G f)
  rw [he] at H
  exact H

/-- Γ+f+g reduces to Γ by actual finite inlining of the two derived programs. -/
def reduction : PolyTimeOracleReduction
    (RawClosedNetwork.validatedEncoding (s+2) 1 arity) F.encoding
    (RawClosedNetwork.validatedEncoding s 1 arity) F.encoding
    (sourceValue G f g) ((GeneralFieldReduction.targetTables F G).evaluate F) :=
  (outerControlled F G f g R).compose (GeneralFieldReduction.reduction F G f P)

theorem source_family_exact :
    Set.range (fun i : Fin (s+2) => (⟨arity i.val,
      Tables.typed (GeneralOriginalQuery.factorTable (extended G f) g) (s+2) arity i⟩ : AnySignature K)) =
      (Set.range (fun i : Fin s => (⟨arity i.val,G i⟩ : AnySignature K)) ∪ {⟨arity s,f⟩}) ∪
        {⟨arity (s+1),g⟩} := by
  rw [GeneralOriginalQuery.source_family_exact, extended, GeneralOriginalQuery.source_family_exact]

end Holant.LocalDrafts.Hardness.GeneralExtraction.RetainedPairReduction
