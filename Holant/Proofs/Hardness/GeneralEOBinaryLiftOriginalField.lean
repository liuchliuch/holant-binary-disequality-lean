import Holant.Proofs.Hardness.EOQuaternaryOriginalSource
import Holant.Proofs.Hardness.EOBinaryPlaneTract
import Holant.Proofs.Hardness.GeneralEOSignedNativeDecoded
import Holant.Proofs.Algorithms.TableFieldTransport

/-! The universal quaternary hardness source is transported into the actual
working coefficient field of a constructed binary row. Generated fields and
answer encodings remain distinct; a real rational-linear retraction is used. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOBinaryLiftOriginalField
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain
namespace B
export EOBinaryPlaneCore (lift lift_eo)
end B
namespace O
export Holant.LocalDrafts.Hardness.EightVertexNonexception.Source
  (coefficient field presentation tables targetValue targetEncoding)
end O
namespace N
export GeneralEOSignedNativeDecoded (nativeValue)
end N
namespace C
export Holant.LocalDrafts.RemoteWork.PlatonicExits.PhysicalCost (composeControlled)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option Elab.async false
variable (K : IntermediateField ℚ AlgebraicComplex)
local instance : Algebra ℚ K := K.algebra'
variable {d : ℕ} (F : FixedField K d) (f : Signature K 2)

def complexRow : Signature AlgebraicComplex 2 := fun z => (f z : AlgebraicComplex)
def lifted : Signature AlgebraicComplex 4 := B.lift (complexRow K f)
theorem algebraic : ∀x,IsAlgebraic ℚ (lifted K f x) := fun _ => Algebra.IsAlgebraic.isAlgebraic _

@[simp] theorem lifted_value (x : Fin 4 → Bool) :
    ((B.lift f x : K) : AlgebraicComplex)=lifted K f x := by
  by_cases h : x 1 = !(x 0) ∧ x 3 = !(x 2) <;>
    simp [B.lift,lifted,complexRow,h]

theorem field_le : O.field (lifted K f) ≤ K := by
  apply IntermediateField.adjoin_le_iff.mpr
  rintro z ⟨c,rfl⟩
  cases c with
  | inl c =>
    change lifted K f c.2 ∈ K
    rw [←lifted_value]
    exact (B.lift f c.2).property
  | inr c =>
    rcases c with ⟨i,a,b⟩
    cases a <;> cases b <;> first | exact K.zero_mem | exact K.one_mem

local instance originalAlgebra : Algebra ℚ (O.field (lifted K f)) :=
  (O.field (lifted K f)).algebra'
def embedding : O.field (lifted K f) →ₐ[ℚ] K := IntermediateField.inclusion (field_le K f)

@[simp] theorem embedding_value (z : O.field (lifted K f)) :
    (embedding K f z : AlgebraicComplex) = z := IntermediateField.coe_inclusion (field_le K f) z

abbrev mappedTables := TableFieldTransport.mapTables
  (O.presentation (lifted K f) (algebraic K f)) F (embedding K f)
  (O.tables (lifted K f) (algebraic K f))

theorem mapped_vertex (i : Fin 1) (x : Fin 4 → Bool) :
    F.decode ((mappedTables K F f).vertex i x)=B.lift f x := by
  apply Subtype.ext
  simp only [mappedTables,TableFieldTransport.mapTables,O.tables,
    FixedGadgetSubstitution.OriginalFamily.tables,
    LinearEquiv.apply_symm_apply,embedding_value,O.presentation,familyCoordinates_spec]
  exact (lifted_value K f x).symm

theorem mapped_edge (i : Fin 1) (a b : Bool) :
    F.decode ((mappedTables K F f).edge i a b)=Signature.disequality a b := by
  apply Subtype.ext
  simp only [mappedTables,TableFieldTransport.mapTables,O.tables,
    FixedGadgetSubstitution.OriginalFamily.tables,
    LinearEquiv.apply_symm_apply,embedding_value,O.presentation,familyCoordinates_spec]
  cases a <;> cases b <;> rfl

theorem mapped_value (r : ExactSignatureTables.Input 1 1 (fun _=>4)) :
    (mappedTables K F f).evaluate F r = N.nativeValue (fun _ : Fin 1 => B.lift f) r := by
  rw [ExactSignatureTables.evaluate_eq_decoded]
  have hv : (fun i x => F.decode ((mappedTables K F f).vertex i x)) =
      (fun _ : Fin 1 => B.lift f) := funext fun i => funext fun x => mapped_vertex K F f i x
  have he : (fun i a b => F.decode ((mappedTables K F f).edge i a b)) =
      (fun _ : Fin 1 => Signature.disequality) :=
    funext fun i => funext fun a => funext fun b => mapped_edge K F f i a b
  rw [hv,he]
  rfl

def fromOriginal : LengthControlledOracleReduction O.targetEncoding
    (O.presentation (lifted K f) (algebraic K f)).encoding
    O.targetEncoding F.encoding (O.targetValue (lifted K f) (algebraic K f))
    (N.nativeValue (fun _ : Fin 1 => B.lift f)) := by
  let r := TableFieldTransport.fromOriginal
    (O.presentation (lifted K f) (algebraic K f)) F (embedding K f)
    (O.tables (lifted K f) (algebraic K f))
  have h := funext (mapped_value K F f)
  rw [h] at r
  exact r

variable (ha : ¬Affine (complexRow K f)) (hp : ¬Product (complexRow K f))
variable {α : Type} {ea : Encoding α Bool} {count : α → ℕ}

def source (w : SharpPWitness ea count) : LengthControlledOracleReduction ea encodingNatBool
    O.targetEncoding F.encoding count (N.nativeValue (fun _ : Fin 1 => B.lift f)) :=
  C.composeControlled
    (EOQuaternaryOriginalSource.source (lifted K f) (B.lift_eo (complexRow K f))
      (fun h => ((EOBinaryPlaneTract.lift_tract_iff (complexRow K f)).mp h).elim ha hp) w)
    (fromOriginal K F f)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOBinaryLiftOriginalField
