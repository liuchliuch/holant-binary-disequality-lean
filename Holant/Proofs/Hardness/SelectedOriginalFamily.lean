import Holant.Proofs.Reductions.EightVertexNonexception.Source
import Holant.Proofs.Reductions.GeneralExtraction.GeneralOriginalTarget
import Holant.Proofs.Reductions.CanonicalFamily.Semantics
import Holant.Proofs.CountingMachines.OracleControl.Storage

/-!
# Literal selected original M to the exact full original G oracle

The physical row map sends singleton label zero to the specified original index.
It copies every ordered port and edge, so equal/duplicate dictionary rows keep
the requested label. The target is the established GeneralOriginalTarget
original-G problem. Its coefficient presentation excludes all macro constants.
An actual fixed rational-matrix programme retracts target answers to the
singleton coefficient field; decoded value equality is never byte equality.
-/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.SelectedOriginalFamily
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity Computability
open BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.Hardness.CanonicalFamily
open Holant.LocalDrafts.BinaryInterpolation.SingularExtraction
namespace Sing
export Holant.LocalDrafts.Hardness.EightVertexNonexception.Source
  (coefficient field presentation targetValue targetEncoding TargetInput target_value_exact)
end Sing
namespace Target
export Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalTarget
  (coefficients originalField originalPresentation originalTables originalValue target_exact)
end Target
namespace Choice
export UniversalPairReduction.Surgery.Choice (table evaluate denote_eq_evaluate)
end Choice
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
variable (M : Signature AlgebraicComplex 4) (j : Fin s)
variable (hj : (⟨a j.val,G j⟩ : AnySignature AlgebraicComplex)=⟨4,M⟩)

theorem algebraic : ∀x,IsAlgebraic ℚ (M x) := fun _=>Algebra.IsAlgebraic.isAlgebraic _
abbrev sourcePresentation := Sing.presentation M (algebraic M)
abbrev sourceValue := Sing.targetValue M (algebraic M)
abbrev targetEncoding := RawClosedNetwork.validatedEncoding s 1 a
abbrev TargetInput := ExactSignatureTables.Input s 1 a
local instance sourceAlgebra : Algebra ℚ (Sing.field M) := (Sing.field M).algebra'
local instance targetAlgebra : Algebra ℚ (Target.originalField G) := (Target.originalField G).algebra'

def label (_ : Fin 1) : Fin s := j

include hj in
theorem arity (i : Fin 1) : a (label j i).val=4 := congrArg Sigma.fst hj

def query : Sing.TargetInput → TargetInput (s:=s) (a:=a) := Relabel.input (label j) (arity G M j hj)

def queryComputes : Computes Sing.targetEncoding (targetEncoding (s:=s) (a:=a)) (query G M j hj) :=
  Relabel.computes (label j) (arity G M j hj)

theorem query_rows (r : Sing.TargetInput) :
    (query G M j hj r).val.vertices=r.val.vertices.map (fun v=>(j.val,v.2)) := by
  change r.val.vertices.map (Relabel.row (label j))=_
  apply List.map_congr_left
  intro v hv
  have hi := (((RawGrouping.wellFormed_iff_members _ _ _ _).mp r.property).1 v hv).1
  simp [query,Relabel.input,Relabel.raw,Relabel.row,Relabel.label,hi,label]

theorem query_ports (r : Sing.TargetInput) :
    (query G M j hj r).val.vertices.map Prod.snd=r.val.vertices.map Prod.snd :=
  Relabel.ordered_ports (label j) r.val

theorem query_edges (r : Sing.TargetInput) : (query G M j hj r).val.edges=r.val.edges := rfl

include hj in
/-- Original coefficients alone imply actual inclusion of the generated fields. -/
theorem field_le : Sing.field M ≤ Target.originalField G := by
  apply IntermediateField.adjoin_le_iff.mpr
  rintro z ⟨i,rfl⟩
  cases i with
  | inl i =>
      have h : ∀x,G j x∈Target.originalField G := fun x=>
        coefficient_mem_familyField (Target.coefficients G) ⟨j,x⟩
      have hM := (congrArg (fun f : AnySignature AlgebraicComplex=>
        ∀x,f.2 x∈Target.originalField G) hj).mp h
      exact hM i.2
  | inr i =>
      rcases i with ⟨i,u,v⟩
      cases u <;> cases v <;> first | exact (Target.originalField G).zero_mem | exact (Target.originalField G).one_mem

def embedding : Sing.field M →ₐ[ℚ] Target.originalField G :=
  IntermediateField.inclusion (field_le G M j hj)

theorem embedding_value (x : Sing.field M) : (embedding G M j hj x : AlgebraicComplex)=x :=
  IntermediateField.coe_inclusion (field_le G M j hj) x

private def read (f : AnySignature AlgebraicComplex) (bits : List Bool) : AlgebraicComplex :=
  f.2 (fun k=>bits.getD k.val false)

include hj in
theorem table_label (i : Fin 1) (bits : List Bool) :
    Choice.table (arity:=fun _=>4) (fun _ : Fin 1=>M) i.val bits=Choice.table G (label j i).val bits := by
  have h := congrArg (fun f=>read f bits) hj
  simpa only [Choice.table,dif_pos i.isLt,dif_pos j.isLt,read,label] using h.symm

theorem ambient_query (r : Sing.TargetInput) :
    ((query G M j hj r).val.realize (query G M j hj r).property G
      (fun _ : Fin 1=>Signature.disequality)).denote Fin.elim0=
    (r.val.realize r.property (fun _ : Fin 1=>M)
      (fun _ : Fin 1=>Signature.disequality)).denote Fin.elim0 := by
  have h := Relabel.value_scaled (label j) (Choice.table (arity:=fun _=>4) (fun _ : Fin 1=>M))
    (Choice.table G) (fun _=>(1 : AlgebraicComplex)) (arity G M j hj) r
    (fun i bits=>by simpa using table_label G M j hj i bits)
  have hp : Holant.LocalDrafts.Hardness.RootPreprocessing.OccurrenceProduct.value
      (fun _ : Fin 1=>(1 : AlgebraicComplex)) r.val=1 := by
    unfold Holant.LocalDrafts.Hardness.RootPreprocessing.OccurrenceProduct.value
    apply List.prod_eq_one
    intro z hz
    obtain ⟨row,hrow,rfl⟩ := List.mem_map.mp hz
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hrow
    simp only [Holant.LocalDrafts.Hardness.RootPreprocessing.OccurrenceProduct.total,
      dif_pos (r.property.1 i).1]
  rw [hp,one_mul] at h
  rw [Choice.denote_eq_evaluate,Choice.denote_eq_evaluate]
  exact h.symm

/-- Equality in the target field is established from the unchanged full
partition function, rather than from any equality between answer encodings. -/
theorem query_value (r : Sing.TargetInput) :
    Target.originalValue G (query G M j hj r)=embedding G M j hj (sourceValue M r) := by
  apply Subtype.ext
  rw [Target.target_exact,embedding_value,Sing.target_value_exact]
  exact ambient_query G M j hj r

def answer := (embedding G M j hj).toLinearMap.leftInverse

def answerComputes : Computes (Target.originalPresentation G).encoding (sourcePresentation M).encoding
    (answer G M j hj) :=
  FieldCodec.retractComputes (sourcePresentation M) (Target.originalPresentation G) (embedding G M j hj)

def controlled : LengthControlledOracleReduction Sing.targetEncoding (sourcePresentation M).encoding
    (targetEncoding (s:=s) (a:=a)) (Target.originalPresentation G).encoding
    (sourceValue M) (Target.originalValue G) :=
  controlledOneQueryOfEq (queryComputes G M j hj) (answerComputes G M j hj)
    ((Target.originalTables G).outputBound (Target.originalPresentation G)) (sourceValue M)
    (fun r=>by
      change sourceValue M r=answer G M j hj (Target.originalValue G (query G M j hj r))
      rw [query_value]
      exact (FieldCodec.retract_embedding (embedding G M j hj) (sourceValue M r)).symm)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.SelectedOriginalFamily
