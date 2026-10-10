import Holant.Proofs.Hardness.GeneralEONegativeTensorCore
import Holant.Proofs.Reductions.GeneralExtraction.GeneralOriginalTarget
import Holant.Complexity.FixedGadgetSubstitution.TemplateFamily
import Holant.Proofs.Algorithms.ControlledReduction

/-! Install the actual arbitrary-arity support tensor as a one-query source.
Both ends use the original family's generated coefficient field, basis and
answer codec. Every input occurrence expands to the literal original labels;
there are no pin/equality resources or promised hardness endpoints. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEONegativeTensorAccess
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedGadgetSubstitution ExactSignatureTables
namespace C
export GeneralEONegativeTensorCore
  (arity graph template valid template_denote template_vertices template_edges)
end C
namespace O
export Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalTarget
  (originalField originalPresentation originalTables originalValue target_exact)
end O
set_option backward.isDefEq.respectTransparency false


variable {s t : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val)) (labels : Fin t→Fin s)
local instance originalAlgebra : Algebra ℚ (O.originalField G) := (O.originalField G).algebra'

abbrev presentation := O.originalPresentation G
abbrev targetEncoding := RawClosedNetwork.validatedEncoding s 1 a
abbrev targetValue := O.originalValue G

abbrev templates (_ : ℕ) : Template := C.template (a:=a) labels
theorem valid : ∀i<1,(templates (a:=a) labels i).WellFormed s 1 a :=
  fun _ _=>C.valid labels

abbrev sourceEncoding := RawClosedNetwork.validatedEncoding 1 1 (sourceArity (templates (a:=a) labels))
abbrev Input := ExactSignatureTables.Input 1 1 (sourceArity (templates (a:=a) labels))
abbrev coordinates := templateCoordinates (presentation G) (templates labels) (valid labels) (O.originalTables G)
abbrev tables := sourceTables (templates labels) (O.originalTables G) (coordinates G labels)
abbrev sourceValue := (tables G labels).evaluate (presentation G)

/-- The literal new coefficient vector is calculated in the original field. -/
theorem coordinates_ambient (i : Fin 1) (x : Fin (C.arity (a:=a) labels)→Bool) :
    ((presentation G).decode (coordinates G labels i x) : AlgebraicComplex)=
      (C.graph labels G).denote x := by
  rw [decode_templateCoordinates]
  have mapped := Network.denote_map (O.originalField G).subtype
    ((templates labels i.val).network (valid labels i.val i.isLt)
      (fun j y=>(presentation G).decode ((O.originalTables G).vertex j y))
      (fun j u v=>(presentation G).decode ((O.originalTables G).edge j u v))) x
  refine mapped.symm.trans ?_
  have hm : (((templates labels i.val).network (valid labels i.val i.isLt)
      (fun j y=>(presentation G).decode ((O.originalTables G).vertex j y))
      (fun j u v=>(presentation G).decode ((O.originalTables G).edge j u v))).map
        (O.originalField G).subtype)=
      (C.template labels).network (C.valid labels) G (fun _ : Fin 1=>Signature.disequality) := by
    unfold Network.map Template.network
    congr 1
    · funext v y
      simp only [O.originalTables,LinearEquiv.apply_symm_apply]
      rfl
    · funext e u v
      simp only [O.originalTables,LinearEquiv.apply_symm_apply]
      cases u <;> cases v <;> rfl
  rw [hm,C.template_denote]

/-- The complete encoded source really evaluates the constructed macro on
arbitrary closed inputs, including repeated vertices, loops and parallel edges. -/
theorem source_value_ambient (r : Input (a:=a) labels) :
    (sourceValue G labels r : AlgebraicComplex)=
      (r.val.realize r.property (fun _ : Fin 1=>(C.graph labels G).denote)
        (fun _ : Fin 1=>Signature.disequality)).denote Fin.elim0 := by
  change (((tables G labels).evaluate (presentation G) r : O.originalField G) : AlgebraicComplex)=_
  rw [ExactSignatureTables.evaluate_eq_decoded]
  change (O.originalField G).subtype _=_
  rw [←Network.denote_map (O.originalField G).subtype]
  congr 1
  unfold Network.map RawClosedNetwork.realize
  congr 1
  · funext v x
    exact coordinates_ambient G labels _ x
  · funext e x y
    simp only [tables,sourceTables,O.originalTables,LinearEquiv.apply_symm_apply]
    cases x <;> cases y <;> rfl

def query := Compiler.value 1 1 (sourceArity (templates (a:=a) labels))
  (templates labels) s a (compilerHypotheses _ (valid labels))
def queryComputes := Compiler.computes 1 1 (sourceArity (templates (a:=a) labels))
  (templates labels) s a (compilerHypotheses _ (valid labels))

theorem query_value (r : Input (a:=a) labels) :
    targetValue G (query labels r)=sourceValue G labels r := by
  have hp := replacement_scale_power (templates labels) r.val r.property (valid labels)
    (fun i x=>(presentation G).decode (coordinates G labels i x))
    (fun j x=>(presentation G).decode ((O.originalTables G).vertex j x))
    (fun j x y=>(presentation G).decode ((O.originalTables G).edge j x y)) 0 (1:O.originalField G)
    (fun i=>by
      simp only [ite_self,one_smul]
      funext x
      exact (decode_templateCoordinates (presentation G) (templates labels) (valid labels)
        (O.originalTables G) i x).symm)
  change targetValue G (query labels r)=1^occurrences 0 r.val*sourceValue G labels r at hp
  simpa only [one_pow,one_mul] using hp

/-- A concrete Boolean compiler, identity answer decoder, polynomial clock,
original answer bound and all-prefix query-size control. -/
def controlled : LengthControlledOracleReduction (sourceEncoding (a:=a) labels) (presentation G).encoding
    (targetEncoding (s:=s) (a:=a)) (presentation G).encoding
    (sourceValue G labels) (targetValue G) :=
  Holant.LocalDrafts.MainChain.controlledOneQueryOfEq (queryComputes labels)
    (identityComputes (presentation G).encoding) ((O.originalTables G).outputBound (presentation G))
    (sourceValue G labels) (fun r=>(query_value G labels r).symm)

/-- Every macro occurrence is replaced separately. Internal edge count does
not grow, and every original input edge keeps its two endpoint occurrences. -/
theorem query_resources (r : Input (a:=a) labels) :
    (query labels r).val.vertices.length=r.val.vertices.length*t ∧
    (query labels r).val.edges.length=r.val.edges.length := by
  constructor
  · rw [query,Compiler.value,replace_vertex_count]
    simp [templates,GeneralEONegativeTensorCore.shape]
  · rw [query,Compiler.value,replace_edge_count]
    simp [templates,GeneralEONegativeTensorCore.shape]

private theorem expanded_labels (offset : ℕ) (rows : List RawVertex) :
    ((expandRows (templates (a:=a) labels) offset rows).vertices.map Prod.fst)=
      (List.replicate rows.length (List.ofFn (fun v : Fin t=>(labels v).val))).flatten := by
  induction rows generalizing offset with
  | nil => rfl
  | cons row rows ih =>
    simp [expandRows,Template.placeVertices,templates,GeneralEONegativeTensorCore.template,
      GeneralEONegativeTensorCore.labelling,Labelling.template,ih,List.replicate_succ,
      Function.comp_def]
    rfl

/-- Repeated original labels are retained as repeated physical rows in the
same fixed order for every source occurrence. -/
theorem query_labels (r : Input (a:=a) labels) :
    ((query labels r).val.vertices.map Prod.fst)=
      (List.replicate r.val.vertices.length (List.ofFn (fun v : Fin t=>(labels v).val))).flatten :=
  expanded_labels labels _ _

/-- Literal edge records, including their labels and original order, are kept. -/
theorem query_edges (r : Input (a:=a) labels) : (query labels r).val.edges=r.val.edges := by
  change (replace (templates labels) r.val).edges=r.val.edges
  simp [replace,expandRows_edges,templates,GeneralEONegativeTensorCore.template,
    Labelling.template,GeneralEONegativeTensorCore.labelling,GeneralEONegativeTensorCore.shape]

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEONegativeTensorAccess
