import Holant.Proofs.Hardness.LabelledNetwork
import Holant.Proofs.Reductions.EightVertexNonexception.Source
import Holant.Proofs.Algorithms.ControlledReduction
import Holant.Proofs.Algorithms.FieldCodec

/-! Generic physical original-port access.
Each permuted-M row becomes one ORIGINAL-M corolla with the exact ordered
boundary p. Original edge IDs and orientations are unchanged. The generated
coefficient presentations are related by derived field inclusion and a real
fixed rational-matrix answer retraction, never by equating decoded bytes.
Final mathematical producers select p from their original coefficient cases;
this reusable compiler itself is correct for every finite permutation. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.OriginalPortAccess
open Holant Holant.Algebraic Holant.Complexity Computability
open BinaryCompose FixedFieldMachines FixedGadgetSubstitution
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.Hardness.EightVertexNonexception
namespace Original
export Holant.LocalDrafts.Hardness.EightVertexNonexception.Source
  (coefficient field fieldSignature coefficient_algebraic presentation tables targetEncoding TargetInput targetValue target_value_exact)
end Original
namespace Chain
export Holant.Complexity.BinaryInterpolation.Chains (reindex reindex_denote)
end Chain
set_option backward.isDefEq.respectTransparency false

variable {L : Type} [Field L] [Algebra ℚ L]
variable (M : Signature L 4) (halg : ∀t,IsAlgebraic ℚ (M t)) (p : Equiv.Perm (Fin 4))

def normalized : Signature L 4 := fun x=>M (fun k=>x (p k))

local instance originalAlgebra : Algebra ℚ (Original.field M) := (Original.field M).algebra'
local instance normalizedAlgebra : Algebra ℚ (Original.field (normalized M p)) :=
  (Original.field (normalized M p)).algebra'

def normalized_algebraic : ∀t,IsAlgebraic ℚ (normalized M p t) :=
  fun t=>halg (fun i=>t (p i))

abbrev sourcePresentation := Original.presentation (normalized M p) (normalized_algebraic M halg p)
abbrev sourceValue := Original.targetValue (normalized M p) (normalized_algebraic M halg p)
abbrev targetPresentation := Original.presentation M halg

def network : Network L 4 := Chain.reindex (Network.corolla M) (p)

def labels : Labelling (network M p).shape 1 1 (fun _=>4) where
  vertex _ := 0
  vertex_arity _ := rfl
  edge := Fin.elim0

abbrev template := (labels M p).template

theorem template_valid : (template M p).WellFormed 1 1 (fun _=>4) := (labels M p).wellFormed

theorem template_records :
    (template M p).boundary=4 ∧
    (template M p).vertices=[(0,List.ofFn fun i : Fin 4=>(Sum.inl (p i).val : LocalEndpoint))] ∧
    (template M p).edges=[] := by
  constructor
  · rfl
  constructor <;> rfl

theorem network_denote : (network M p).denote=normalized M p := by
  rw [network,Chain.reindex_denote,Network.denote_corolla]
  rfl

theorem template_denote :
    ((template M p).network (template_valid M p) (fun _ : Fin 1=>M)
      (fun _ : Fin 1=>Signature.disequality)).denote=normalized M p := by
  calc
    _ = (network M p).denote := by
      apply Labelling.denote_template_of_labels (labels M p) _ _ (network M p).vertex (network M p).edge
      · intro v x; rfl
      · intro e; exact Fin.elim0 e
    _ = _ := network_denote M p

def templates (_ : ℕ) : Template := template M p

def templateHypotheses : ∀i<1,(templates M p i).WellFormed 1 1 (fun _=>4) ∧
    (templates M p i).boundary=4 := fun _ _=>⟨template_valid M p,rfl⟩

def query : Original.TargetInput → Original.TargetInput :=
  Compiler.value 1 1 (fun _=>4) (templates M p) 1 (fun _=>4) (templateHypotheses M p)

def queryComputes : Computes Original.targetEncoding Original.targetEncoding (query M p) :=
  Compiler.computes 1 1 (fun _=>4) (templates M p) 1 (fun _=>4) (templateHypotheses M p)

theorem query_raw (r : Original.TargetInput) : (query M p r).val=replace (templates M p) r.val := rfl

/-- Each old M port i receives exactly incoming boundary port permutation(i).
The compiler keeps original edge IDs and orientations; only row positions move. -/
def permuteRow (row : RawVertex) : RawVertex :=
  (0,List.ofFn fun i : Fin 4=>row.2.getD (p i).val (0,false))

private theorem placed_row (offset : ℕ) (row : RawVertex) :
    (template M p).placeVertices offset row.2=[permuteRow p row] := by
  simp only [Template.placeVertices,(template_records M p).2.1,List.map_singleton,
    List.map_ofFn,permuteRow]
  rfl

private theorem expanded_rows (rows : List RawVertex) (offset : ℕ) :
    (expandRows (templates M p) offset rows).vertices=rows.map (permuteRow p) := by
  induction rows generalizing offset with
  | nil => rfl
  | cons row rows ih =>
      simp only [expandRows,templates,placed_row,List.singleton_append,List.map_cons]
      rw [ih]

private theorem expanded_edges (rows : List RawVertex) (offset : ℕ) :
    (expandRows (templates M p) offset rows).edges=[] := by
  induction rows generalizing offset with
  | nil => rfl
  | cons row rows ih =>
      simp only [expandRows,templates,(template_records M p).2.2,List.nil_append]
      exact ih _

theorem query_rows (r : Original.TargetInput) :
    (query M p r).val.vertices=r.val.vertices.map (permuteRow p) := expanded_rows M p _ _

theorem query_edges (r : Original.TargetInput) : (query M p r).val.edges=r.val.edges := by
  change r.val.edges++(expandRows (templates M p) r.val.edges.length r.val.vertices).edges=_
  rw [expanded_edges,List.append_nil]

theorem query_vertex_count (r : Original.TargetInput) :
    (query M p r).val.vertices.length=r.val.vertices.length := by rw [query_rows,List.length_map]

/-- Literal original coefficients, merely reordered, belong to the original
field. The normalized native-X generator contributes only zero or one. -/
theorem field_le : Original.field (normalized M p) ≤ Original.field M := by
  apply IntermediateField.adjoin_le_iff.mpr
  rintro z ⟨i,rfl⟩
  cases i with
  | inl i =>
      exact coefficient_mem_familyField (Original.coefficient M)
        (.inl ⟨0,fun k=>i.2 (p k)⟩)
  | inr i =>
      rcases i with ⟨i,u,v⟩
      cases u <;> cases v <;> first | exact (Original.field M).zero_mem | exact (Original.field M).one_mem

def embedding : Original.field (normalized M p) →ₐ[ℚ] Original.field M :=
  IntermediateField.inclusion (field_le M p)

theorem embedding_value (x : Original.field (normalized M p)) :
    (embedding M p x : L)=x := IntermediateField.coe_inclusion (field_le M p) x

theorem ambient_query (r : Original.TargetInput) :
    ((query M p r).val.realize (query M p r).property (fun _ : Fin 1=>M)
      (fun _ : Fin 1=>Signature.disequality)).denote Fin.elim0=
    (r.val.realize r.property (fun _ : Fin 1=>normalized M p)
      (fun _ : Fin 1=>Signature.disequality)).denote Fin.elim0 := by
  have h := replacement_scale_power (templates M p) r.val r.property
    (fun _ _=>template_valid M p) (fun _ : Fin 1=>normalized M p)
    (fun _ : Fin 1=>M) (fun _ : Fin 1=>Signature.disequality) 0 (1 : L)
    (fun _=>by simpa only [templates,ite_self,one_smul] using template_denote M p)
  simpa only [one_pow,one_mul] using h

/-- Full query value equality in the original field, prior to actual answer
retraction. This does not equate the two independently generated codecs. -/
theorem query_value (r : Original.TargetInput) :
    Original.targetValue M halg (query M p r)=embedding M p (sourceValue M halg p r) := by
  apply Subtype.ext
  rw [Original.target_value_exact,embedding_value,Original.target_value_exact]
  exact ambient_query M p r

def answer := (embedding M p).toLinearMap.leftInverse

def answerComputes : Computes (targetPresentation M halg).encoding (sourcePresentation M halg p).encoding
    (answer M p) :=
  FieldCodec.retractComputes (sourcePresentation M halg p) (targetPresentation M halg) (embedding M p)

/-- Physical normalized-singleton to SAME original-singleton oracle access.
No normalization premise is needed for this finite permutation compiler itself. -/
def controlled : LengthControlledOracleReduction Original.targetEncoding (sourcePresentation M halg p).encoding
    Original.targetEncoding (targetPresentation M halg).encoding
    (sourceValue M halg p) (Original.targetValue M halg) :=
  controlledOneQueryOfEq (queryComputes M p) (answerComputes M halg p)
    ((Original.tables M halg).outputBound (targetPresentation M halg)) (sourceValue M halg p)
    (fun r=>by
      change sourceValue M halg p r=answer M p (Original.targetValue M halg (query M p r))
      rw [query_value]
      exact (FieldCodec.retract_embedding (embedding M p) (sourceValue M halg p r)).symm)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.OriginalPortAccess
