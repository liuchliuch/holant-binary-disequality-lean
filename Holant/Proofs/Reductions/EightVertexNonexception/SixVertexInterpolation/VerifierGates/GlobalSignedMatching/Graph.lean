import Holant.Proofs.Reductions.EightVertexNonexception.SixVertexInterpolation.VerifierGates.GlobalSignedMatching.Cycle
import Holant.Proofs.Hardness.VerifierInputCore
import Holant.Proofs.Reductions.EightVertexNonexception.SixVertexInterpolation.VerifierGates.WeightedMatchingInterpolation.Network


namespace Holant.LocalDrafts.Hardness.EightVertexNonexception.SixVertexInterpolation.VerifierGates.GlobalSignedMatching
open Computability Holant Holant.Complexity
open FixedFieldMachines
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

abbrev Occurrence := ℕ × DualRail.VerifierInput.Literal
def occurrenceEncoding := pairEncoding encodingNatBool DualRail.VerifierInput.literalEncoding

/-- The clause index is retained, and the global position in this list is
the literal occurrence ID. Equal literals still have distinct list indices. -/
def occurrences (q : DualRail.VerifierInput.Input) : List Occurrence :=
  (List.range q.2.length).flatMap (fun c => (q.2.getD c []).map (fun l => (c,l)))
def occurrence (q : DualRail.VerifierInput.Input) (j : ℕ) : Occurrence := (occurrences q).getD j (0,(0,false))
abbrev slots (q : DualRail.VerifierInput.Input) : ℕ := (occurrences q).length+1
def base (q : DualRail.VerifierInput.Input) : ℕ := (q.1+q.2.length)*slots q
def vertexCount (q : DualRail.VerifierInput.Input) : ℕ := base q+4*(occurrences q).length
def variableVertex (q : DualRail.VerifierInput.Input) (v j : ℕ) : ℕ := v*slots q+j
def clauseVertex (q : DualRail.VerifierInput.Input) (c j : ℕ) : ℕ := q.1*slots q+c*slots q+j
def xorVertex (q : DualRail.VerifierInput.Input) (j r : ℕ) : ℕ := base q+4*j+r
def nextSlot (q : DualRail.VerifierInput.Input) (j : ℕ) : ℕ :=
  if j<(occurrences q).length then j+1 else 0

/-- `forward=false` means the diagonal occurrence; `true` the forward
occurrence. A positive literal marks a diagonal edge, a negative a forward
edge. Only that ONE original occurrence is removed and replaced by XOR. -/
def isMarked (q : DualRail.VerifierInput.Input) (v j : ℕ) (forward : Bool) : Bool :=
  decide (j<(occurrences q).length) &&
    (occurrence q j).2.1==v && forward==!(occurrence q j).2.2

def variableRecord (q : DualRail.VerifierInput.Input) (v j : ℕ) (forward : Bool) : WeightedMatchingInterpolation.SignedEdge :=
  ((variableVertex q v j,variableVertex q v (if forward then nextSlot q j else j)),false)
def variableBlock (q : DualRail.VerifierInput.Input) (v j : ℕ) : List WeightedMatchingInterpolation.SignedEdge :=
  (if isMarked q v j false then [] else [variableRecord q v j false]) ++
  (if isMarked q v j true then [] else [variableRecord q v j true])
def variableEdges (q : DualRail.VerifierInput.Input) : List WeightedMatchingInterpolation.SignedEdge :=
  (List.range q.1).flatMap (fun v =>
    (List.range (slots q)).flatMap (variableBlock q v))

def clauseBlock (q : DualRail.VerifierInput.Input) (c j : ℕ) : List WeightedMatchingInterpolation.SignedEdge :=
  [((clauseVertex q c j,clauseVertex q c j),false),
   ((clauseVertex q c j,clauseVertex q c (nextSlot q j)),decide (j=(occurrences q).length))]
def clauseEdges (q : DualRail.VerifierInput.Input) : List WeightedMatchingInterpolation.SignedEdge :=
  (List.range q.2.length).flatMap (fun c =>
    (List.range (slots q)).flatMap (clauseBlock q c))

def xorLocal : List WeightedMatchingInterpolation.SignedEdge :=
  ValiantXor.activeEdges.map (fun e => ((e.1.val,e.2.val),decide (ValiantXor.matrix e.1 e.2=-1)))
def xorRecord (q : DualRail.VerifierInput.Input) (j : ℕ) (e : WeightedMatchingInterpolation.SignedEdge) : WeightedMatchingInterpolation.SignedEdge :=
  ((xorVertex q j e.1.1,xorVertex q j e.1.2),e.2)
def xorEdges (q : DualRail.VerifierInput.Input) : List WeightedMatchingInterpolation.SignedEdge :=
  (List.range (occurrences q).length).flatMap (fun j => xorLocal.map (xorRecord q j))

/-- The first connection replaces the marked variable edge; the second
occupies a literal's clause row/column pair. Each connection consists of TWO
real graph edges. No fourth XOR port or auxiliary vertex disappears. -/
def connectors (q : DualRail.VerifierInput.Input) (j : ℕ) : List WeightedMatchingInterpolation.SignedEdge :=
  let o := occurrence q j
  let target := if o.2.2 then j else nextSlot q j
  [((variableVertex q o.2.1 j,xorVertex q j 0),false),
   ((xorVertex q j 0,variableVertex q o.2.1 target),false),
   ((clauseVertex q o.1 j,xorVertex q j 1),false),
   ((xorVertex q j 1,clauseVertex q o.1 j),false)]
def connectorEdges (q : DualRail.VerifierInput.Input) : List WeightedMatchingInterpolation.SignedEdge :=
  (List.range (occurrences q).length).flatMap (connectors q)
def raw (q : DualRail.VerifierInput.Input) : WeightedMatchingInterpolation.Raw :=
  (vertexCount q,variableEdges q++clauseEdges q++xorEdges q++connectorEdges q)

theorem occurrences_member (q : DualRail.VerifierInput.Input) (o : Occurrence) : o∈occurrences q ↔
    ∃ c,c<q.2.length ∧ ∃ l,l∈q.2.getD c [] ∧ (c,l)=o := by
  simp [occurrences,List.mem_flatMap,List.mem_map,List.mem_range]
theorem occurrence_member (q : DualRail.VerifierInput.Input) (j : ℕ) (hj : j<(occurrences q).length) :
    occurrence q j∈occurrences q := by
  rw [occurrence,List.getD_eq_getElem _ _ hj]
  exact List.getElem_mem hj
theorem occurrence_clause (q : DualRail.VerifierInput.Input) (j : ℕ) (hj : j<(occurrences q).length) :
    (occurrence q j).1<q.2.length := by
  obtain ⟨c,hc,l,_,he⟩ := (occurrences_member q _).mp (occurrence_member q j hj)
  simpa only [← he] using hc
theorem occurrence_variable (q : DualRail.VerifierInput.Input) (hq : DualRail.VerifierInput.Bounded q) (j : ℕ)
    (hj : j<(occurrences q).length) : (occurrence q j).2.1<q.1 := by
  obtain ⟨c,hc,l,hl,he⟩ := (occurrences_member q _).mp (occurrence_member q j hj)
  rw [List.getD_eq_getElem _ _ hc] at hl
  have hb := hq _ (List.getElem_mem hc) l hl
  simpa only [← he] using hb

theorem nextSlot_lt (q : DualRail.VerifierInput.Input) (j : ℕ) : nextSlot q j<slots q := by
  unfold nextSlot slots
  split <;> omega
theorem nextSlot_rotate (q : DualRail.VerifierInput.Input) (j : Fin (slots q)) :
    nextSlot q j.val=(Cycle.next (occurrences q).length j).val := by
  by_cases hj : j.val<(occurrences q).length
  · rw [nextSlot,if_pos hj,Cycle.next,finRotate_of_lt hj]
  · have hj' := j.isLt
    change j.val<(occurrences q).length+1 at hj'
    have he : j=Fin.last (occurrences q).length := Fin.ext (by simpa only [Fin.val_last] using (show j.val = (occurrences q).length from by omega))
    rw [he,Cycle.next,finRotate_last]
    simp [nextSlot]

theorem variableVertex_lt (q : DualRail.VerifierInput.Input) (v j : ℕ) (hv : v<q.1) (hj : j<slots q) :
    variableVertex q v j<vertexCount q := by
  have hs : (v+1)*slots q≤q.1*slots q := Nat.mul_le_mul_right _ (by omega)
  dsimp [variableVertex,vertexCount,base]
  nlinarith
theorem clauseVertex_lt (q : DualRail.VerifierInput.Input) (c j : ℕ) (hc : c<q.2.length) (hj : j<slots q) :
    clauseVertex q c j<vertexCount q := by
  have hs : (c+1)*slots q≤q.2.length*slots q := Nat.mul_le_mul_right _ (by omega)
  dsimp [clauseVertex,vertexCount,base]
  nlinarith
theorem xorVertex_lt (q : DualRail.VerifierInput.Input) (j r : ℕ) (hj : j<(occurrences q).length) (hr : r<4) :
    xorVertex q j r<vertexCount q := by
  dsimp [xorVertex,vertexCount]
  omega

theorem variableBlock_valid (q : DualRail.VerifierInput.Input) (v j : ℕ) (hv : v<q.1) (hj : j<slots q)
    (e : WeightedMatchingInterpolation.SignedEdge) (he : e∈variableBlock q v j) :
    e.1.1<vertexCount q ∧ e.1.2<vertexCount q := by
  have hd := variableVertex_lt q v j hv hj
  have hs := variableVertex_lt q v (nextSlot q j) hv (nextSlot_lt q j)
  have he' : e=variableRecord q v j false ∨ e=variableRecord q v j true := by
    unfold variableBlock at he
    split at he <;> split at he <;> simp_all
  rcases he' with rfl | rfl
  · exact ⟨hd,hd⟩
  · exact ⟨hd,hs⟩

theorem clauseBlock_valid (q : DualRail.VerifierInput.Input) (c j : ℕ) (hc : c<q.2.length) (hj : j<slots q)
    (e : WeightedMatchingInterpolation.SignedEdge) (he : e∈clauseBlock q c j) :
    e.1.1<vertexCount q ∧ e.1.2<vertexCount q := by
  have hd := clauseVertex_lt q c j hc hj
  have hs := clauseVertex_lt q c (nextSlot q j) hc (nextSlot_lt q j)
  simp only [clauseBlock,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at he
  rcases he with rfl | rfl <;> exact ⟨hd,by assumption⟩

theorem xorLocal_bounds (e : WeightedMatchingInterpolation.SignedEdge) (he : e∈xorLocal) : e.1.1<4 ∧ e.1.2<4 := by
  obtain ⟨p,_,rfl⟩ := List.mem_map.mp he
  exact ⟨p.1.isLt,p.2.isLt⟩
theorem connectors_valid (q : DualRail.VerifierInput.Input) (hq : DualRail.VerifierInput.Bounded q) (j : ℕ)
    (hj : j<(occurrences q).length) (e : WeightedMatchingInterpolation.SignedEdge) (he : e∈connectors q j) :
    e.1.1<vertexCount q ∧ e.1.2<vertexCount q := by
  have hv := occurrence_variable q hq j hj
  have hc := occurrence_clause q j hj
  have hj' : j<slots q := by unfold slots; omega
  have vd := variableVertex_lt q _ j hv hj'
  have vs := variableVertex_lt q _ (nextSlot q j) hv (nextSlot_lt q j)
  have cd := clauseVertex_lt q _ j hc hj'
  have x₀ := xorVertex_lt q j 0 hj (by decide)
  have x₁ := xorVertex_lt q j 1 hj (by decide)
  simp only [connectors,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact ⟨vd,x₀⟩
  · refine ⟨x₀,?_⟩
    split <;> assumption
  · exact ⟨cd,x₁⟩
  · exact ⟨x₁,cd⟩

theorem raw_valid (q : DualRail.VerifierInput.Input) (hq : DualRail.VerifierInput.Bounded q) : WeightedMatchingInterpolation.Valid (raw q) := by
  intro e he
  simp only [raw,List.mem_append,or_assoc] at he
  rcases he with he | he | he | he
  · obtain ⟨v,hv,j,hj,he⟩ : ∃ v,v<q.1 ∧ ∃ j,j<slots q ∧ e∈variableBlock q v j := by
      simpa [variableEdges,List.mem_flatMap,List.mem_range] using he
    exact variableBlock_valid q v j hv hj e he
  · obtain ⟨c,hc,j,hj,he⟩ : ∃ c,c<q.2.length ∧ ∃ j,j<slots q ∧ e∈clauseBlock q c j := by
      simpa [clauseEdges,List.mem_flatMap,List.mem_range] using he
    exact clauseBlock_valid q c j hc hj e he
  · obtain ⟨j,hj,p,hp,rfl⟩ : ∃ j,j<(occurrences q).length ∧ ∃ p,p∈xorLocal ∧ xorRecord q j p=e := by
      simpa [xorEdges,List.mem_flatMap,List.mem_map,List.mem_range] using he
    have hb := xorLocal_bounds p hp
    exact ⟨xorVertex_lt q j _ hj hb.1,xorVertex_lt q j _ hj hb.2⟩
  · obtain ⟨j,hj,he⟩ : ∃ j,j<(occurrences q).length ∧ e∈connectors q j := by
      simpa [connectorEdges,List.mem_flatMap,List.mem_range] using he
    exact connectors_valid q hq j hj e he

abbrev Input := {q : DualRail.VerifierInput.Input // DualRail.VerifierInput.Bounded q}
instance (q : DualRail.VerifierInput.Input) : Decidable (DualRail.VerifierInput.Bounded q) := by unfold DualRail.VerifierInput.Bounded; infer_instance
def encoding : Encoding Input Bool where
  encode q := DualRail.VerifierInput.encoding.encode q.val
  decode bits := do
    let q ← DualRail.VerifierInput.encoding.decode bits
    if h : DualRail.VerifierInput.Bounded q then some ⟨q,h⟩ else none
  decode_encode q := by simp [q.property]
def graph (q : Input) : WeightedMatchingInterpolation.Input := ⟨raw q.val,raw_valid q.val q.property⟩

theorem xorRecord_weight (q : DualRail.VerifierInput.Input) (j : ℕ) (e : ValiantXor.Edge) :
    (if (xorRecord q j ((e.1.val,e.2.val),decide (ValiantXor.matrix e.1 e.2=-1))).2
      then (-1 : ℤ) else 1)=ValiantXor.matrix e.1 e.2 ∨ ValiantXor.matrix e.1 e.2=0 := by
  rcases e with ⟨r,c⟩
  simp only [xorRecord]
  fin_cases r <;> fin_cases c <;> norm_num [ValiantXor.matrix]
theorem xorRecord_active_weight (q : DualRail.VerifierInput.Input) (j : ℕ) (e : ValiantXor.Edge) (he : e∈ValiantXor.activeEdges) :
    (if (xorRecord q j ((e.1.val,e.2.val),decide (ValiantXor.matrix e.1 e.2=-1))).2
      then (-1 : ℤ) else 1)=ValiantXor.matrix e.1 e.2 := by
  rcases xorRecord_weight q j e with h | h
  · exact h
  · exact False.elim (((ValiantXor.template_edges_exact e).mp he) h)

theorem marked_dummy (q : DualRail.VerifierInput.Input) (v : ℕ) (b : Bool) :
    isMarked q v (occurrences q).length b=false := by simp [isMarked]
theorem connectors_length (q : DualRail.VerifierInput.Input) (j : ℕ) : (connectors q j).length=4 := rfl
theorem xorLocal_length : xorLocal.length=10 := by decide
theorem raw_size (q : DualRail.VerifierInput.Input) :
    (raw q).2.length≤2*(q.1+q.2.length)*slots q+14*(occurrences q).length := by
  have variableBound (v : ℕ) :
      ((List.range (slots q)).flatMap (variableBlock q v)).length≤2*slots q := by
    rw [List.length_flatMap]
    calc
      _≤((List.range (slots q)).map (fun _ => 2)).sum := by
        apply List.sum_le_sum
        intro j hj
        unfold variableBlock
        split <;> split <;> simp
      _=_ := by simp [Nat.mul_comm]
  have hv : (variableEdges q).length≤q.1*(2*slots q) := by
    rw [variableEdges,List.length_flatMap]
    calc
      _≤((List.range q.1).map (fun _ => 2*slots q)).sum := by
        exact List.sum_le_sum (fun v _ => variableBound v)
      _=_ := by simp [Nat.mul_comm]
  have hc : (clauseEdges q).length=q.2.length*(slots q*2) := by
    simp [clauseEdges,List.length_flatMap,clauseBlock,Nat.mul_comm]
  have hx : (xorEdges q).length=(occurrences q).length*10 := by
    simp [xorEdges,List.length_flatMap,xorLocal_length]
  have hi : (connectorEdges q).length=(occurrences q).length*4 := by
    simp [connectorEdges,List.length_flatMap,connectors_length]
  simp only [raw,List.length_append,hc,hx,hi]
  nlinarith

end Holant.LocalDrafts.Hardness.EightVertexNonexception.SixVertexInterpolation.VerifierGates.GlobalSignedMatching
