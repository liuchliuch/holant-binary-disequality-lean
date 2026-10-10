import Holant.Proofs.Algorithms.BinaryQueryControl
import Holant.Proofs.Algorithms.TableFieldTransport


namespace Holant.LocalDrafts.MainChain.BinaryOriginalTarget
open Holant.Certificates.MatchingContractionClosure
open Computability Holant.Algebraic Holant.Complexity
open Holant.Complexity.BinaryInterpolation
open Holant.LocalDrafts.BinaryInterpolation
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {s : ℕ} {arity : ℕ → ℕ}
variable (G : (i : Fin s) → Signature ℂ (arity i.val))
variable (halg : ∀ i x, IsAlgebraic ℚ (G i x))

abbrev OriginalIndex := Σ i : Fin s, (Fin (arity i.val) → Bool)
def coefficients (i : OriginalIndex (s:=s) (arity:=arity)) : ℂ := G i.1 i.2
include halg in
theorem coefficients_algebraic (i : OriginalIndex (s:=s) (arity:=arity)) :
    IsAlgebraic ℚ (coefficients G i) := halg i.1 i.2

abbrev originalField := familyField (coefficients G)
abbrev originalPresentation := familyPresentation (coefficients G) (coefficients_algebraic G halg)

def originalTables : ExactSignatureTables (Module.finrank ℚ (originalField G)) s 1 arity where
  vertex i x := (originalPresentation G halg).decode.symm (fieldCoefficient (coefficients G) ⟨i,x⟩)
  edge _ a b := (originalPresentation G halg).decode.symm (Signature.disequality a b)

abbrev originalValue := (originalTables G halg).evaluate (originalPresentation G halg)

variable {B : Binary (K:=ℂ)} (M : AlgebraicSource.Macro G B)
variable (p : AlgebraicSource.Pencil M.binary)

theorem field_le : originalField G ≤ AlgebraicSource.CommonField.field G M.binary p := by
  apply IntermediateField.adjoin_le_iff.mpr
  rintro z ⟨i,rfl⟩
  exact coefficient_mem_familyField
    (AlgebraicSource.CommonField.coefficient G M.binary p) (.inl i)

def embedding : originalField G →ₐ[ℚ] AlgebraicSource.CommonField.field G M.binary p :=
  IntermediateField.inclusion (field_le G M p)

theorem mapped_tables :
    TableFieldTransport.mapTables (originalPresentation G halg) (FieldSource.fixedField G halg M p)
      (embedding G M p) (originalTables G halg) = FieldSource.targetTables G halg M p := by
  unfold TableFieldTransport.mapTables originalTables FieldSource.targetTables
  congr 1
  · funext i x
    rw [LinearEquiv.apply_symm_apply]
    rfl
  · funext i a b
    rw [LinearEquiv.apply_symm_apply]
    congr 1
    cases a <;> cases b <;> simp [Signature.disequality]

def targetTransport : LengthControlledOracleReduction
    (FieldSource.targetEncoding (s:=s) (arity:=arity)) (FieldSource.outputEncoding G halg M p)
    (FieldSource.targetEncoding (s:=s) (arity:=arity)) (originalPresentation G halg).encoding
    (AlgebraicSource.CommonField.targetValue G M.binary p) (originalValue G halg) := by
  have h := TableFieldTransport.toOriginal (originalPresentation G halg)
    (FieldSource.fixedField G halg M p) (embedding G M p) (originalTables G halg)
  rw [mapped_tables G halg M p] at h
  have he : (FieldSource.targetTables G halg M p).evaluate (FieldSource.fixedField G halg M p) =
      AlgebraicSource.CommonField.targetValue G M.binary p :=
    funext (FieldSource.target_evaluate G halg M p)
  rw [he] at h
  exact h

/-- The full interpolation machine now calls the oracle in the original
family's own codec. Every sample remains a literal original-family graph. -/
def reduction : PolyTimeOracleReduction
    (FieldSource.inputEncoding (s:=s) (arity:=arity)) (FieldSource.outputEncoding G halg M p)
    (FieldSource.targetEncoding (s:=s) (arity:=arity)) (originalPresentation G halg).encoding
    (AlgebraicSource.CommonField.sourceValue G M.binary p) (originalValue G halg) :=
  (BinaryQueryControl.controlled G halg M p).compose (targetTransport G halg M p).reduction

theorem target_value_exact (r : ExactSignatureTables.Input s 1 arity) :
    ((originalValue G halg r : originalField G) : ℂ) =
      (r.val.realize r.property G (fun _ : Fin 1 => Signature.disequality)).denote Fin.elim0 := by
  rw [originalValue, ExactSignatureTables.evaluate_eq_decoded]
  change (originalField G).subtype _ = _
  rw [← Network.denote_map (originalField G).subtype]
  congr 1
  unfold Network.map RawClosedNetwork.realize
  congr 1
  · funext v x
    simp only [originalTables, LinearEquiv.apply_symm_apply]
    rfl
  · funext e a b
    simp only [originalTables, LinearEquiv.apply_symm_apply]
    cases a <;> cases b <;> rfl

end
end Holant.LocalDrafts.MainChain.BinaryOriginalTarget
