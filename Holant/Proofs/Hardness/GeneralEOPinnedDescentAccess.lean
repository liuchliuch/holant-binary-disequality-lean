import Holant.Proofs.Hardness.GeneralEOPinnedDescentLabels
import Holant.Proofs.Algorithms.MacroTransport

/-! The actual fixed labelled graph has a literal replacement compiler over
the same coefficient field. Every emitted graph is validated, and graph sizes,
coordinate decoding and query provenance are proved from the graph itself. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPinnedDescentAccess
open Computability Holant Holant.Complexity Holant.Algebraic
open FixedGadgetSubstitution ExactSignatureTables BinaryCompose
set_option backward.isDefEq.respectTransparency false
variable {K : Type} [Field K] [Algebra ℚ K] {n s d : ℕ} {a : ℕ → ℕ}
variable (F : FixedField K d) (G : (i : Fin s) → Signature K (a i.val))
variable (S : Network K n) (L : Labelling S.shape s 1 a)
variable (he : LabelledNetwork.Exact G S L) (hn : ∀e,S.edge e=Signature.disequality)

def tables : ExactSignatureTables d s 1 a where
  vertex i x := F.decode.symm (G i x)
  edge _ u v := F.decode.symm (Signature.disequality u v)

abbrev templates (_ : ℕ) : Template := L.template
abbrev valid : ∀i<1,(templates S L i).WellFormed s 1 a := fun _ _ => L.wellFormed

omit [Algebra ℚ K] in
include he hn in
theorem template_denote :
    (L.template.network L.wellFormed G (fun _ : Fin 1 => Signature.disequality)).denote=S.denote := by
  apply Labelling.denote_template_of_labels L G (fun _ : Fin 1 => Signature.disequality) S.vertex S.edge
  · intro v x
    have h := he v
    have aux {m k : ℕ} (f : Signature K m) (g : Signature K k)
        (hf : (⟨m,f⟩ : AnySignature K)=⟨k,g⟩) (ha : m=k) (y : Fin k → Bool) :
        f (fun i => y (Fin.cast ha i))=g y := by
      cases hf
      rfl
    exact aux _ _ h (L.vertex_arity v) x
  · intro e u v
    exact congrFun₂ (hn e).symm u v

def coordinates (i : Fin 1) (x : Fin n → Bool) : Fin d → ℚ :=
  templateCoordinates F (templates S L) (valid S L) (tables F G) i x

include he hn in
theorem coordinates_exact (i : Fin 1) (x : Fin n → Bool) :
    F.decode (coordinates F G S L i x)=S.denote x := by
  rw [coordinates,decode_templateCoordinates]
  simp only [tables,LinearEquiv.apply_symm_apply]
  exact congrFun (template_denote G S L he hn) x

def query := Compiler.value 1 1 (fun _ => n) (templates S L) s a
  (compilerHypotheses _ (valid S L))
def queryComputes := Compiler.computes 1 1 (fun _ => n) (templates S L) s a
  (compilerHypotheses _ (valid S L))

def sourceTables : ExactSignatureTables d 1 1 (fun _ => n) where
  vertex _ x := F.decode.symm (S.denote x)
  edge _ u v := F.decode.symm (Signature.disequality u v)

def sourceValue := (sourceTables F S).evaluate F
def targetValue := (tables F G).evaluate F

include he hn in
theorem query_value (q : Input 1 1 (fun _ => n)) :
    targetValue F G (query S L q)=sourceValue F S q := by
  have hp := replacement_scale_power (templates S L) q.val q.property (valid S L)
    (fun _ : Fin 1 => S.denote) G (fun _ : Fin 1 => Signature.disequality) 0 (1 : K)
    (fun _ => by simpa only [ite_self,one_smul] using template_denote G S L he hn)
  simp only [one_pow,one_mul] at hp
  change (tables F G).evaluate F _=(sourceTables F S).evaluate F _
  rw [ExactSignatureTables.evaluate_eq_decoded,ExactSignatureTables.evaluate_eq_decoded]
  simpa only [tables,sourceTables,LinearEquiv.apply_symm_apply] using hp

/-- Same field, same answer codec, one compiled native-X query. -/
def source : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding 1 1 (fun _ => n)) F.encoding
    (RawClosedNetwork.validatedEncoding s 1 a) F.encoding
    (sourceValue F S) (targetValue F G) :=
  Holant.LocalDrafts.MainChain.controlledOneQueryOfEq (queryComputes S L)
    (identityComputes F.encoding) ((tables F G).outputBound F) (sourceValue F S)
    (fun q => (query_value F G S L he hn q).symm)

omit [Field K] [Algebra ℚ K] in
theorem query_counts (q : Input 1 1 (fun _ => n)) :
    (query S L q).val.vertices.length=q.val.vertices.length*S.shape.vertices ∧
    (query S L q).val.edges.length=q.val.edges.length+q.val.vertices.length*S.shape.edges := by
  change (replace (templates S L) q.val).vertices.length=_ ∧ (replace (templates S L) q.val).edges.length=_
  rw [replace_vertex_count,replace_edge_count]
  simp [templates,Labelling.vertices_length,Labelling.edges_length]

omit [Field K] [Algebra ℚ K] in
/-- Serialized occurrence counts retain each actual label independently. -/
theorem template_occurrences (j : Fin s) :
    (L.template.vertices.filter (fun row => row.1=j.val)).length=LabelledNetwork.count L j :=
  LabelledNetwork.template_count L j

/-- Every reached oracle call parses as the unchanged target palette. -/
theorem query_parses (oracle : List Bool → List Bool)
    (ho : RepresentsOracle (RawClosedNetwork.validatedEncoding s 1 a) F.encoding (targetValue F G) oracle)
    (q : Input 1 1 (fun _ => n)) (t : ℕ) (z : (source F G S L he hn).reduction.machine.Cfg)
    (hr : (source F G S L he hn).reduction.machine.run oracle
      ((RawClosedNetwork.validatedEncoding 1 1 (fun _ => n)).encode q) t=some z)
    (hq : (source F G S L he hn).reduction.machine.IsQuery z) :
    ∃r : Input s 1 a,
      z.stk (source F G S L he hn).reduction.machine.queryStack=
        (RawClosedNetwork.validatedEncoding s 1 a).encode r ∧
      (RawClosedNetwork.validatedEncoding s 1 a).decode
        (z.stk (source F G S L he hn).reduction.machine.queryStack)=some r := by
  obtain ⟨r,hw,_⟩ := (source F G S L he hn).safeQuery oracle ho q t z hr hq
  refine ⟨r,hw,?_⟩
  rw [hw]
  exact (RawClosedNetwork.validatedEncoding s 1 a).decode_encode r

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPinnedDescentAccess
