import Holant.Proofs.BinaryInterpolation.SingularExtraction.CommonField
import Holant.Proofs.Algorithms.FamilyFieldInclusion
import Holant.Proofs.Algorithms.TableFieldTransport


noncomputable section
namespace Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.Composition.OriginalField
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.Complexity.BinaryCompose Holant.Complexity.FixedFieldMachines
open Holant.LocalDrafts.MainChain
set_option backward.isDefEq.respectTransparency false
variable {s : ℕ} {arity : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (arity i.val))

abbrev Index := Σ i : Fin s, (Fin (arity i.val) → Bool)
def coefficient (i : Index (s:=s) (arity:=arity)) : AlgebraicComplex := G i.1 i.2
theorem algebraic (i : Index (s:=s) (arity:=arity)) : IsAlgebraic ℚ (coefficient G i) :=
  Algebra.IsAlgebraic.isAlgebraic _
abbrev field := familyField (coefficient G)
abbrev presentation := familyPresentation (coefficient G) (algebraic G)
abbrev original (i : Fin s) (x : Fin (arity i.val) → Bool) : field G :=
  fieldCoefficient (coefficient G) ⟨i,x⟩
def tables : ExactSignatureTables (Module.finrank ℚ (field G)) s 1 arity where
  vertex i x := (presentation G).decode.symm (original G i x)
  edge _ a b := (presentation G).decode.symm (Signature.disequality a b)
abbrev value := (tables G).evaluate (presentation G)
abbrev encoding := (presentation G).encoding

theorem value_exact (q : ExactSignatureTables.Input s 1 arity) :
    (value G q : AlgebraicComplex) =
      (q.val.realize q.property G (fun _ => Signature.disequality)).denote Fin.elim0 := by
  rw [value, ExactSignatureTables.evaluate_eq_decoded]
  change (field G).subtype _ = _
  rw [← Network.denote_map]
  congr 1
  unfold Network.map RawClosedNetwork.realize
  congr 1
  · funext v x
    simp only [tables,LinearEquiv.apply_symm_apply]
    rfl
  · funext e a b
    simp only [tables,LinearEquiv.apply_symm_apply]
    cases a <;> cases b <;> rfl

variable (u v : Bool → AlgebraicComplex) (U : PowerMacro G u) (V : PowerMacro G v)
def extra : ((Bool × Bool) ⊕ Bool) → AlgebraicComplex
  | .inl (q,a) => if q then v a else u a
  | .inr q => if q then V.scale else U.scale

theorem combined_eq : FamilyFieldInclusion.combined (coefficient G) (extra G u v U V) =
    CommonField.coefficient G u v U V := by
  funext i
  rcases i with ⟨i,x⟩ | (⟨q,a⟩ | q) <;> rfl

theorem field_le : field G ≤ CommonField.field G u v U V := by
  have h := FamilyFieldInclusion.field_le (coefficient G) (extra G u v U V)
  rw [combined_eq] at h
  exact h
def embedding : field G →ₐ[ℚ] CommonField.field G u v U V :=
  IntermediateField.inclusion (field_le G u v U V)

theorem mapped_tables : TableFieldTransport.mapTables (presentation G)
    (CommonField.presentation G u v U V) (embedding G u v U V) (tables G) =
    FieldReduction.targetTables (CommonField.presentation G u v U V) (CommonField.original G u v U V) := by
  unfold TableFieldTransport.mapTables tables FieldReduction.targetTables
  congr 1
  · funext i x
    rw [LinearEquiv.apply_symm_apply]
    rfl
  · funext i a b
    rw [LinearEquiv.apply_symm_apply]
    congr 1
    cases a <;> cases b <;> simp [Signature.disequality]

theorem target_eq (q : ExactSignatureTables.Input s 1 arity) :
    CommonField.targetValue G u v U V q = embedding G u v U V (value G q) := by
  have h := TableFieldTransport.evaluate_map (presentation G)
    (CommonField.presentation G u v U V) (embedding G u v U V) (tables G) q
  rw [mapped_tables] at h
  exact h

def embedComputes : Computes (encoding G) (CommonField.presentation G u v U V).encoding
    (embedding G u v U V) :=
  FieldCodec.computes (presentation G) (CommonField.presentation G u v U V)
    (embedding G u v U V).toLinearMap

def transport : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding s 1 arity) (CommonField.presentation G u v U V).encoding
    (RawClosedNetwork.validatedEncoding s 1 arity) (encoding G)
    (CommonField.targetValue G u v U V) (value G) := by
  have h := TableFieldTransport.toOriginal (presentation G) (CommonField.presentation G u v U V)
    (embedding G u v U V) (tables G)
  rw [mapped_tables] at h
  exact h

/-- Cost of the actual rational matrix program, not semantic application of
the field embedding treated as an instruction. -/
theorem conversion_primitive (x : field G) :
    primitiveCost (embedComputes G u v U V).machine ((embedComputes G u v U V).outputs x).steps
      (some (Turing.initList (embedComputes G u v U V).machine.computer ((encoding G).encode x))) ≤
      (primitivePolynomial (embedComputes G u v U V)).eval ((encoding G).encode x).length :=
  computes_primitive_cost (embedComputes G u v U V) x

end Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.Composition.OriginalField
