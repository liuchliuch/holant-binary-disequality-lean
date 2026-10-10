import Holant.Proofs.Tetrahedral.OrdinaryReplication.Raw
import Holant.Proofs.Algorithms.QuaternaryReplicationCompiler


noncomputable section
attribute [local instance] Classical.propDecidable
namespace Holant.LocalDrafts.TetrahedralCompletion.OrdinaryReplication
open Computability Holant.Complexity Holant.Algebraic Holant.Tractable
open BinaryCompose FixedFieldMachines GraphPreprocessing
open GraphPreprocessing.OriginalCoefficient RawClosedNetwork
open FixedGadgetSubstitution FixedGadgetSubstitution.Compiler UniversalPairReduction
open Holant.LocalDrafts.MainChain
set_option backward.isDefEq.respectTransparency false

private theorem count_append_alias (s : ℕ) (xs ys : List RawVertex) :
    count s (xs++ys)=count s xs+count s ys :=
  QuaternaryReplicationCompiler.count_append s xs ys

theorem expand_carrier (s j4 m : ℕ) (rows : List RawVertex) :
    (expand s j4 m rows).carrierPort=(m+count s rows,false) ∧
      (expand s j4 m rows).otherPort=(m,true) := by
  induction rows with
  | nil => simp [expand,count,QuaternaryReplicationMachine.count]
  | cons row rows ih =>
      by_cases h : row.1=s
      · simp only [expand,if_pos h,graft,count_cons,if_pos h]
        rw [expand_next,ih.2]
        constructor
        · apply Prod.ext <;> simp <;> omega
        · rfl
      · simpa [expand,h,count_cons] using ih

def emitRow (s j4 m t : ℕ) (row : RawVertex) : List RawVertex :=
  if row.1=s then
    [(j4,[(m+1+t,true),(m+t,false),row.2.getD 0 (0,false),row.2.getD 1 (0,false)])]
  else [row]

theorem expand_body (s j4 m : ℕ) (rows : List RawVertex) :
    (expand s j4 m rows).body=(List.finRange rows.length).flatMap
      (fun i => emitRow s j4 m (count s (rows.drop (i.val+1))) (rows.get i)) := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      simp only [List.length_cons,List.finRange_succ,List.flatMap_cons,List.flatMap_map,
        Function.comp_def,Fin.val_zero,Fin.val_succ,List.get_eq_getElem,
        List.getElem_cons_zero,List.getElem_cons_succ,List.drop_succ_cons,List.drop_zero]
      by_cases h : row.1=s
      · simp only [expand,if_pos h,emitRow,if_pos h,graft,List.cons_append,List.nil_append]
        rw [expand_next,(expand_carrier s j4 m rows).1,ih]
        rfl
      · simpa only [expand,if_neg h,emitRow,if_neg h,List.cons_append,List.nil_append,List.get_eq_getElem] using
          congrArg (List.cons row) ih

variable (s : ℕ) (a : ℕ → ℕ)
abbrev RowQuery := FixedGadgetSubstitution.Compiler.Query (s+1) 1 (extendedArity s a)
abbrev rowEncoding := queryEncoding (s+1) 1 (extendedArity s a)
abbrev sourceEncoding := validatedEncoding (s+1) 1 (extendedArity s a)
def suffix (x : RowQuery s a) : ℕ := count s (x.1.val.vertices.drop (x.2.val+1))

theorem suffix_sub (x : RowQuery s a) : suffix s a x=
    count s x.1.val.vertices-
      (prefixWeight (s+1) 1 (extendedArity s a) (fun i => if i=s then 1 else 0) x+
        if (x.1.val.vertices.get x.2).1=s then 1 else 0) := by
  have he : x.1.val.vertices=x.1.val.vertices.take x.2.val++
      (x.1.val.vertices.get x.2::x.1.val.vertices.drop (x.2.val+1)) := by
    rw [List.cons_get_drop_succ,List.take_append_drop]
  have hc := congrArg (count s) he
  rw [count_append_alias,count_cons] at hc
  unfold suffix prefixWeight
  rw [indicator_sum]
  change count s _=count s _-(count s _+_)
  omega

def countComputes : Computes (sourceEncoding s a) UnaryBinary.unaryEncoding
    (fun r : Input s a => count s r.val.vertices) :=
  occurrencesComputes (s:=s+1) (b:=1) (arity:=extendedArity s a) s

def suffixComputes : Computes (rowEncoding s a) encodingNatBool (suffix s a) := by
  let total := ((sourceComputes (s+1) 1 (extendedArity s a)).andThen
    (countComputes s a)).andThen UnaryBinary.computes
  let before := (prefixWeightComputes (s+1) 1 (extendedArity s a)
    (fun i => if i=s then 1 else 0)).andThen UnaryBinary.computes
  let current := labelRecodeComputes (s+1) 1 (extendedArity s a) encodingNatBool
    (fun i => if i.val=s then 1 else 0)
  exact congrComputes (QuaternaryReplicationCompiler.sub total
    (QuaternaryReplicationCompiler.add before current)) (fun x => (suffix_sub s a x).symm)

def rowEdgeComputes : Computes (rowEncoding s a) encodingNatBool
    (fun x => x.1.val.edges.length) :=
  ((sourceComputes (s+1) 1 (extendedArity s a)).andThen
    (edgeCountComputes (s+1) 1 (extendedArity s a))).andThen UnaryBinary.computes
def portsComputes : Computes (rowEncoding s a) (framedListEncoding endpointEncoding)
    (fun x => (x.1.val.vertices.get x.2).2) :=
  (originalRowComputes (s+1) 1 (extendedArity s a)).andThen
    (recode (Wiring.secondComputes encodingNatBool (framedListEncoding endpointEncoding))
      id (fun _ => rfl) (fun _ => rfl))

/-- Every endpoint ID is computed by an existing Boolean arithmetic program.
The two original endpoints retain their order; padding is raw.graft's padding. -/
def replacementComputes (j4 : ℕ) : Computes (rowEncoding s a) vertexEncoding
    (fun x => (j4,[(x.1.val.edges.length+1+suffix s a x,true),
      (x.1.val.edges.length+suffix s a x,false),
      (x.1.val.vertices.get x.2).2.getD 0 (0,false),
      (x.1.val.vertices.get x.2).2.getD 1 (0,false)])) := by
  let e := rowEncoding s a
  let endpoint (i : Fin 4) (x : RowQuery s a) : RawEndpoint :=
    if i.val=0 then (x.1.val.edges.length+1+suffix s a x,true)
    else if i.val=1 then (x.1.val.edges.length+suffix s a x,false)
    else (x.1.val.vertices.get x.2).2.getD (i.val-2) (0,false)
  have ep (i : Fin 4) : Computes e endpointEncoding (endpoint i) := by
    refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => Fin.cases ?_
      (fun i => Fin.cases ?_ (fun i => Fin.elim0 i) i) i) i) i
    · exact recode (pairComputes
        (QuaternaryReplicationCompiler.add
          (QuaternaryReplicationCompiler.add (rowEdgeComputes s a) (constantComputes e encodingNatBool 1))
          (suffixComputes s a)) (constantComputes e encodingBoolBool true))
          id (fun _ => rfl) (fun _ => rfl)
    · exact recode (pairComputes
        (QuaternaryReplicationCompiler.add (rowEdgeComputes s a) (suffixComputes s a))
        (constantComputes e encodingBoolBool false)) id (fun _ => rfl) (fun _ => rfl)
    · exact (portsComputes s a).andThen (getDComputes endpointEncoding 0 (0,false))
    · exact (portsComputes s a).andThen (getDComputes endpointEncoding 1 (0,false))
  exact congrComputes (recode (pairComputes (constantComputes e encodingNatBool j4)
    (fixedListComputes e endpointEncoding (fun x i => endpoint i x) ep (List.finRange 4)))
      id (fun _ => rfl) (fun _ => rfl))
    (fun x => by simp [endpoint,List.finRange_succ])

def rowChunk (j4 : ℕ) (x : RowQuery s a) : List Bool :=
  entries vertexEncoding (emitRow s j4 x.1.val.edges.length (suffix s a x) (x.1.val.vertices.get x.2))
def rowChunkComputes (j4 : ℕ) : Computes (rowEncoding s a) Frame.wordEncoding (rowChunk s a j4) := by
  let original := (originalRowComputes (s+1) 1 (extendedArity s a)).andThen (entryComputes vertexEncoding)
  let replaced := (replacementComputes s a j4).andThen (entryComputes vertexEncoding)
  apply congrComputes (chooseComputes (rowEncoding s a) Frame.wordEncoding (s+1)
    (sourceLabel (s+1) 1 (extendedArity s a))
    (fun x i => if i.val=s then entry vertexEncoding
      (j4,[(x.1.val.edges.length+1+suffix s a x,true),(x.1.val.edges.length+suffix s a x,false),
        (x.1.val.vertices.get x.2).2.getD 0 (0,false),(x.1.val.vertices.get x.2).2.getD 1 (0,false)])
      else entry vertexEncoding (x.1.val.vertices.get x.2))
    (labelRecodeComputes (s+1) 1 (extendedArity s a) UnaryBinary.unaryEncoding Fin.val)
    (fun i => by
      by_cases hi : i.val=s
      · exact congrComputes replaced (fun x => by simp [hi])
      · exact congrComputes original (fun x => by simp [hi])))
  intro x
  by_cases h : (x.1.val.vertices.get x.2).1=s <;>
    simp only [List.get_eq_getElem] at h <;>
    simp [rowChunk,emitRow,sourceLabel,entries,h]

def headComputes : Computes (sourceEncoding s a) vertexEncoding
    (fun r => (s,[(r.val.edges.length+count s r.val.vertices,false),(r.val.edges.length,true)])) := by
  let m := (edgeCountComputes (s+1) 1 (extendedArity s a)).andThen UnaryBinary.computes
  let k := (countComputes s a).andThen UnaryBinary.computes
  let port0 := recode (pairComputes (QuaternaryReplicationCompiler.add m k)
    (constantComputes (sourceEncoding s a) encodingBoolBool false))
    id (fun _ => rfl) (fun _ => rfl)
  let port1 := recode (pairComputes m (constantComputes (sourceEncoding s a) encodingBoolBool true))
    id (fun _ => rfl) (fun _ => rfl)
  let ps := fixedListComputes (sourceEncoding s a) endpointEncoding
    (fun r b => if b then (r.val.edges.length,true) else (r.val.edges.length+count s r.val.vertices,false))
    (fun b => by cases b; exact port0; exact port1) [false,true]
  exact recode (pairComputes (constantComputes (sourceEncoding s a) encodingNatBool s) ps)
    id (fun _ => rfl) (fun _ => rfl)

def verticesComputes (j4 : ℕ) : Computes (sourceEncoding s a) (framedListEncoding vertexEncoding)
    (fun r => (raw s j4 r.val).vertices) := by
  let head := (headComputes s a).andThen (entryComputes vertexEncoding)
  let body := allRowsFlatMapComputes (s+1) 1 (extendedArity s a) _ (rowChunkComputes s a j4)
  refine recode (joinComputes (joinComputes head body)
    (constantComputes (sourceEncoding s a) Frame.wordEncoding [false])) id (fun _ => rfl) ?_
  intro r
  have hb : (List.finRange r.val.vertices.length).flatMap (fun i => rowChunk s a j4 ⟨r,i⟩)=
      entries vertexEncoding (expand s j4 r.val.edges.length r.val.vertices).body := by
    rw [expand_body,entries_flatMap]
    rfl
  change (_++_)++[false]=framedListEncode vertexEncoding (raw s j4 r.val).vertices
  dsimp only [id_eq,Function.comp_def]
  rw [hb]
  have h := entries_append_encode vertexEncoding
    ((s,[(r.val.edges.length+count s r.val.vertices,false),(r.val.edges.length,true)])::
      (expand s j4 r.val.edges.length r.val.vertices).body) []
  simpa [raw,emitted,(expand_carrier s j4 r.val.edges.length r.val.vertices).1,
    (expand_carrier s j4 r.val.edges.length r.val.vertices).2,
    entries,List.flatMap_cons,List.append_assoc,framedListEncode] using h

def edgesComputes : Computes (sourceEncoding s a) (framedListEncoding encodingNatBool)
    (fun r => (raw s 0 r.val).edges) := by
  let old := (FixedGadgetSubstitution.Compiler.edgesComputes (s+1) 1 (extendedArity s a)).andThen
    (entriesComputes encodingNatBool)
  let added := allRowsFlatMapComputes (s+1) 1 (extendedArity s a) _
    (labelRecodeComputes (s+1) 1 (extendedArity s a) Frame.wordEncoding
      (fun i => entries encodingNatBool (if i.val=s then [0] else [])))
  let initial := constantComputes (sourceEncoding s a) Frame.wordEncoding (entry encodingNatBool 0)
  refine recode (joinComputes (joinComputes (joinComputes old initial) added)
    (constantComputes (sourceEncoding s a) Frame.wordEncoding [false])) id (fun _ => rfl) ?_
  intro r
  have hc (rows : List RawVertex) :
      rows.flatMap (fun row => if row.1=s then [0] else [])=List.replicate (count s rows) 0 := by
    induction rows with
    | nil => rfl
    | cons row rows ih =>
        by_cases h : row.1=s <;> simp [h,QuaternaryReplicationMachine.count_cons,ih,List.replicate_add]
  have ha : (List.finRange r.val.vertices.length).flatMap (fun i =>
      entries encodingNatBool (if (r.val.vertices.get i).1=s then [0] else []))=
      entries encodingNatBool (List.replicate (count s r.val.vertices) 0) := by
    rw [←entries_flatMap]
    have he := congrArg (fun rows : List RawVertex => rows.flatMap
      (fun row => if row.1=s then [0] else [])) (all_rows (s+1) 1 (extendedArity s a) r)
    rw [List.flatMap_map] at he
    rw [he,hc]
  change ((entries encodingNatBool r.val.edges++entry encodingNatBool 0)++_)++[false]=_
  dsimp only [id_eq,sourceLabel]
  rw [ha]
  have he := entries_append_encode encodingNatBool
    (r.val.edges++(0::List.replicate (count s r.val.vertices) 0)) []
  simpa [raw,entries,List.flatMap_append,List.flatMap_cons,entry,List.append_assoc,
    List.replicate_add,framedListEncode,framedListEncoding] using he

def rawComputes (j4 : ℕ) : Computes (sourceEncoding s a) RawClosedNetwork.encoding
    (fun r => raw s j4 r.val) :=
  recode (pairComputes (verticesComputes s a j4) (edgesComputes s a))
    id (fun _ => rfl) (fun _ => rfl)

/-- Same bytes, vertex order, old edge prefix and fresh IDs as the raw graft's query. -/
def queryComputes (j4 : Fin s) (h4 : a j4.val=4) :
    Computes (sourceEncoding s a) (UniversalPairReduction.inputEncoding s a) (query j4 h4) :=
  recode (rawComputes s a j4.val) id (fun _ => rfl) (fun _ => rfl)

theorem query_length (j4 : Fin s) (h4 : a j4.val=4) (r : Input s a) :
    ((UniversalPairReduction.inputEncoding s a).encode (query j4 h4 r)).length≤
      (queryComputes s a j4 h4).outputBound.bound.eval ((sourceEncoding s a).encode r).length :=
  (queryComputes s a j4 h4).outputBound.length_le r

/-- Runtime is derived from the finite Boolean-stack program, not from
query_length or the linear vertex-count estimate. -/
theorem query_runtime (j4 : Fin s) (h4 : a j4.val=4) (r : Input s a) :
    primitiveCost (queryComputes s a j4 h4).machine ((queryComputes s a j4 h4).outputs r).steps
      (some (Turing.initList (queryComputes s a j4 h4).machine.computer
        ((sourceEncoding s a).encode r)))≤
      (primitivePolynomial (queryComputes s a j4 h4)).eval ((sourceEncoding s a).encode r).length :=
  computes_primitive_cost (queryComputes s a j4 h4) r

section Caller
variable {K : Type} [Field K] [Algebra ℚ K] {d : ℕ}
variable (F : FixedField K d) (G : (i : Fin s) → Signature K (a i.val))
variable (j4 : Fin s)
variable (h4 : (⟨a j4.val,G j4⟩ : AnySignature K)=⟨4,Holant.EightVertex.ProductAnchor.equalityFour⟩)
variable (j : Bool)

def carrierTables : ExactSignatureTables d (s+1) 1 (extendedArity s a) where
  vertex i x := F.decode.symm (BinaryFamily.signatures G (QuaternaryOrdinaryCompanion.pair G j) i x)
  edge _ b c := F.decode.symm (Signature.equality b c)
theorem carrier_tables_value (r : UniversalPairReduction.Input s a) :
    (carrierTables s a F G j).evaluate F ⟨r.val,r.property.1⟩=
      QuaternaryOrdinaryCompanion.value G (QuaternaryOrdinaryCompanion.pair G j) r := by
  rw [ExactSignatureTables.evaluate_eq_decoded]
  simp only [carrierTables,LinearEquiv.apply_symm_apply]
  rfl
def carrierAnswerBound : PolynomialOutputBound (UniversalPairReduction.inputEncoding s a) F.encoding
    (QuaternaryOrdinaryCompanion.value G (QuaternaryOrdinaryCompanion.pair G j)) where
  bound := (carrierTables s a F G j).outputPolynomial F
  length_le r := by
    have h := (carrierTables s a F G j).output_length_le F ⟨r.val,r.property.1⟩
    rw [carrier_tables_value s a F G j r] at h
    exact h

def pre (r : Input s a) := ([query j4 (congrArg Sigma.fst h4) r],false)
def preComputes : Computes (sourceEncoding s a)
    (OracleBatch.contextEncoding (UniversalPairReduction.inputEncoding s a) encodingBoolBool)
    (pre s a G j4 h4) :=
  pairComputes (fixedListComputes (sourceEncoding s a) (UniversalPairReduction.inputEncoding s a)
    (fun r (_ : Bool) => query j4 (congrArg Sigma.fst h4) r)
    (fun _ => queryComputes s a j4 (congrArg Sigma.fst h4)) [false])
    (constantComputes (sourceEncoding s a) encodingBoolBool false)
def post (p : List K×Bool) : K := (QuaternaryOrdinaryCompanion.companion G j j)⁻¹*p.1.getD 0 0
def postComputes : Computes (OracleBatch.contextEncoding F.encoding encodingBoolBool) F.encoding
    (post s a G j) :=
  congrComputes (scaleComputes F
    ((Wiring.firstComputes (framedListEncoding F.encoding) encodingBoolBool).andThen
      (getDComputes F.encoding 0 0)) (QuaternaryOrdinaryCompanion.companion G j j)⁻¹)
    (fun p => mul_comm _ _)

theorem recovery (r : Input s a) :
    sourceValue G j r=post s a G j (OracleBatch.answers
      (QuaternaryOrdinaryCompanion.value G (QuaternaryOrdinaryCompanion.pair G j)) (pre s a G j4 h4 r)) := by
  simp only [pre,post,OracleBatch.answers,List.map_cons,List.map_nil,List.getD_cons_zero]
  rw [query_value G j4 h4 j r,←mul_assoc,
    inv_mul_cancel₀ (QuaternaryOrdinaryCompanion.companion_nonzero G j),one_mul]

/-- One controlled call to the actual at-most-one companion oracle. Its
answer bound is derived from the same ordinary table and SAME field codec. -/
def controlled : LengthControlledOracleReduction (sourceEncoding s a) F.encoding
    (UniversalPairReduction.inputEncoding s a) F.encoding (sourceValue G j)
    (QuaternaryOrdinaryCompanion.value G (QuaternaryOrdinaryCompanion.pair G j)) := by
  have he : sourceValue G j=fun r => post s a G j (OracleBatch.answers
      (QuaternaryOrdinaryCompanion.value G (QuaternaryOrdinaryCompanion.pair G j)) (pre s a G j4 h4 r)) :=
    funext (recovery s a G j4 h4 j)
  rw [he]
  exact TraceQueryControl.controlledBatch (preComputes s a G j4 h4) (postComputes s a F G j)
    (carrierAnswerBound s a F G j)

end Caller

section Anchor
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
variable (A : QuaternaryEqualityTerminal.AnchorStep (UniversalPairReduction.FiniteFamily.family G))
local instance : Algebra ℚ (QuaternaryAnchorAccess.K G A) := (QuaternaryAnchorAccess.K G A).algebra'

abbrev anchorInputEncoding := sourceEncoding (s+1) (QuaternaryAnchorAccess.arity G A)
abbrev anchorValue (j : Bool) := sourceValue (QuaternaryOrdinaryCompanion.decoded G A) j
def anchorControlled (j : Bool) : LengthControlledOracleReduction
    (anchorInputEncoding s a G A) (QuaternaryOrdinaryCompanion.anchorField G A).encoding
    (QuaternaryOrdinaryCompanion.anchorInputEncoding G A) (QuaternaryOrdinaryCompanion.anchorField G A).encoding
    (anchorValue s a G A j) (QuaternaryOrdinaryCompanion.anchorValue G A j) :=
  controlled (s+1) (QuaternaryAnchorAccess.arity G A) (QuaternaryOrdinaryCompanion.anchorField G A)
    (QuaternaryOrdinaryCompanion.decoded G A) (QuaternaryOrdinaryCompanion.eq4Index (s:=s))
    (QuaternaryOrdinaryCompanion.decoded_eq4 G A) j

abbrev Access (j : Bool) := PolyTimeOracleReduction
    (anchorInputEncoding s a G A) (QuaternaryOrdinaryCompanion.anchorField G A).encoding
    (QuaternaryAnchorAccess.targetEncoding (s:=s) (a:=a))
    (QuaternaryAnchorAccess.GOT.originalPresentation G).encoding
    (anchorValue s a G A j) (QuaternaryAnchorAccess.GOT.originalValue G)

/-- The existing companion and anchor terminal execute INSIDE this controlled
caller. This does not compose two arbitrary Poly reductions. -/
def access (j : Bool) : Access s a G A j :=
  (anchorControlled s a G A j).compose (QuaternaryOrdinaryCompanion.access G A j)

def execution (j : Bool) (oracle : List Bool → List Bool)
    (ho : RepresentsOracle (QuaternaryAnchorAccess.targetEncoding (s:=s) (a:=a))
      (QuaternaryAnchorAccess.GOT.originalPresentation G).encoding
      (QuaternaryAnchorAccess.GOT.originalValue G) oracle)
    (r : Input (s+1) (QuaternaryAnchorAccess.arity G A)) :=
  (access s a G A j).correct oracle ho r

section OriginalL
open Holant.LocalDrafts.Hardness.FrozenFactorNormalization
variable {L : Type} [Field L] [NumberField L]
variable (φ : L →ₐ[ℚ] AlgebraicComplex) (H : (i : Fin s) → Signature L (a i.val))
variable (B : QuaternaryEqualityTerminal.AnchorStep
  (UniversalPairReduction.FiniteFamily.family (OriginalLCodec.mapped φ H)))
def accessOriginalL (j : Bool) : PolyTimeOracleReduction
    (anchorInputEncoding s a (OriginalLCodec.mapped φ H) B)
    (QuaternaryOrdinaryCompanion.anchorField (OriginalLCodec.mapped φ H) B).encoding
    (RawClosedNetwork.validatedEncoding s 1 a) (OriginalLCodec.presentation (L:=L)).encoding
    (anchorValue s a (OriginalLCodec.mapped φ H) B j) (OriginalLCodec.value H) :=
  (anchorControlled s a (OriginalLCodec.mapped φ H) B j).compose
    (QuaternaryOrdinaryCompanion.accessOriginalL φ H B j)
end OriginalL
end Anchor
end Holant.LocalDrafts.TetrahedralCompletion.OrdinaryReplication
