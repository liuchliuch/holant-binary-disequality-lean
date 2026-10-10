import Holant.Algebraic.RationalEncoding
import Holant.Complexity.FixedFieldMachines.PairEncoding
import Holant.Complexity.FramedEncoding
import Holant.Complexity.GraphPreprocessing.UnaryBinary
import Mathlib.Data.List.Nodup
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic


namespace Holant.LocalDrafts.Hardness.EightVertexNonexception.SixVertexInterpolation.VerifierGates.WeightedMatchingInterpolation
open Computability Holant Holant.Algebraic Holant.Complexity
open scoped BigOperators
open FixedFieldMachines GraphPreprocessing
set_option backward.isDefEq.respectTransparency false

abbrev SignedEdge := (ℕ × ℕ) × Bool
abbrev Raw := ℕ × List SignedEdge
def edgeEncoding := pairEncoding (pairEncoding encodingNatBool encodingNatBool) encodingBoolBool
def rawEncoding := pairEncoding UnaryBinary.unaryEncoding (framedListEncoding edgeEncoding)
def Valid (g : Raw) : Prop := ∀ e ∈ g.2,e.1.1<g.1 ∧ e.1.2<g.1
instance (g : Raw) : Decidable (Valid g) := by unfold Valid; infer_instance
abbrev Input := {g : Raw // Valid g}
def encoding : Encoding Input Bool where
  encode g := rawEncoding.encode g.val
  decode bits := do
    let g ← rawEncoding.decode bits
    if h : Valid g then some ⟨g,h⟩ else none
  decode_encode g := by simp [g.property]

/-- The first pair is an edge ID, the second pair its original endpoints. -/
abbrev UnitEdge := (ℕ × ℕ) × (ℕ × ℕ)
abbrev UnitRaw := ℕ × List UnitEdge
def unitEdgeEncoding := pairEncoding (pairEncoding encodingNatBool encodingNatBool)
  (pairEncoding encodingNatBool encodingNatBool)
def unitRawEncoding := pairEncoding UnaryBinary.unaryEncoding (framedListEncoding unitEdgeEncoding)
def UnitValid (g : UnitRaw) : Prop := g.2.Nodup ∧ ∀ e ∈ g.2,e.2.1<g.1 ∧ e.2.2<g.1
instance (g : UnitRaw) : Decidable (UnitValid g) := by unfold UnitValid; infer_instance
abbrev UnitInput := {g : UnitRaw // UnitValid g}
def unitEncoding : Encoding UnitInput Bool where
  encode g := unitRawEncoding.encode g.val
  decode bits := do
    let g ← unitRawEncoding.decode bits
    if h : UnitValid g then some ⟨g,h⟩ else none
  decode_encode g := by simp [g.property]

def multiplicity (g : Raw) (k i : ℕ) : ℕ := if (g.2.getD i ((0,0),false)).2 then k else 1
def copyEdge (g : Raw) (i j : ℕ) : UnitEdge := ((i,j),(g.2.getD i ((0,0),false)).1)
def block (g : Raw) (k i : ℕ) : List UnitEdge :=
  (List.range (multiplicity g k i)).map (copyEdge g i)
def queryRaw (g : Raw) (k : ℕ) : UnitRaw :=
  (g.1,(List.range g.2.length).flatMap (block g k))

theorem query_member (g : Raw) (k : ℕ) (e : UnitEdge) :
    e ∈ (queryRaw g k).2 ↔
      ∃ i,i<g.2.length ∧ ∃ j,j<multiplicity g k i ∧ copyEdge g i j=e := by
  simp only [queryRaw,List.mem_flatMap,block,List.mem_map,List.mem_range]

theorem query_nodup (g : Raw) (k : ℕ) : (queryRaw g k).2.Nodup := by
  apply List.nodup_flatMap.mpr
  constructor
  · intro i _
    apply (List.nodup_range).map
    intro a b h
    exact congrArg (fun e : UnitEdge => e.1.2) h
  · apply (List.nodup_range).imp
    intro i j hij e he hj
    obtain ⟨a,_,ha⟩ := List.mem_map.mp he
    obtain ⟨b,_,hb⟩ := List.mem_map.mp hj
    apply hij
    exact congrArg (fun e : UnitEdge => e.1.1) (ha.trans hb.symm)

theorem query_valid (g : Input) (k : ℕ) : UnitValid (queryRaw g.val k) := by
  refine ⟨query_nodup g.val k,?_⟩
  intro e he
  obtain ⟨i,hi,j,_,rfl⟩ := (query_member g.val k e).mp he
  exact g.property _ (by
    rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem hi)

def query (g : Input) (k : ℕ) : UnitInput := ⟨queryRaw g.val k,query_valid g k⟩
theorem query_vertices (g : Input) (k : ℕ) : (query g k).val.1=g.val.1 := rfl
theorem query_occurrence (g : Input) (k i j : ℕ) (hi : i<g.val.2.length)
    (hj : j<multiplicity g.val k i) : copyEdge g.val i j ∈ (query g k).val.2 :=
  (query_member g.val k _).mpr ⟨i,hi,j,hj,rfl⟩
theorem query_identifiers (g : Raw) (i j : ℕ) : (copyEdge g i j).1=(i,j) := rfl
theorem query_endpoints (g : Raw) (i j : ℕ) :
    (copyEdge g i j).2=(g.2.getD i ((0,0),false)).1 := rfl

noncomputable section

/-- One edge incident to EACH row, and one preimage at EACH column.
The row order makes this a unique representation of an ordinary matching.
-/
def Perfect {E : Type} (n : ℕ) (left right : E → ℕ) (f : Fin n → E) : Prop :=
  (∀ r,left (f r)=r.val) ∧ ∀ c : Fin n,∃! r : Fin n,right (f r)=c.val
abbrev OriginalEdges (g : Input) := Fin g.val.2.length
def originalEdge (g : Input) (i : OriginalEdges g) : SignedEdge := g.val.2.get i
abbrev Matching (g : Input) := {f : Fin g.val.1 → OriginalEdges g //
  Perfect g.val.1 (fun e => (originalEdge g e).1.1) (fun e => (originalEdge g e).1.2) f}
instance (g : Input) : Fintype (Matching g) := by
  classical
  unfold Matching
  infer_instance
abbrev UnitEdges (g : UnitInput) := {e : UnitEdge // e ∈ g.val.2.toFinset}
instance (g : UnitInput) : Fintype (UnitEdges g) := by unfold UnitEdges; infer_instance
abbrev UnitMatching (g : UnitInput) := {f : Fin g.val.1 → UnitEdges g //
  Perfect g.val.1 (fun e => e.val.2.1) (fun e => e.val.2.2) f}
instance (g : UnitInput) : Fintype (UnitMatching g) := by
  classical
  unfold UnitMatching
  infer_instance
def unitCount (g : UnitInput) : ℕ := Fintype.card (UnitMatching g)

def copies (g : Input) (k : ℕ) (i : OriginalEdges g) : ℕ := if (originalEdge g i).2 then k else 1
abbrev Copies (g : Input) (k : ℕ) := Σ i : OriginalEdges g,Fin (copies g k i)

theorem copies_eq (g : Input) (k : ℕ) (i : OriginalEdges g) :
    copies g k i=multiplicity g.val k i.val := by
  simp only [copies,multiplicity,originalEdge,List.getD_eq_getElem _ _ i.isLt,List.get_eq_getElem]

private theorem unit_edge_spec (g : Input) (k : ℕ) (e : UnitEdges (query g k)) :
    e.val.1.1<g.val.2.length ∧ e.val.1.2<multiplicity g.val k e.val.1.1 ∧
      copyEdge g.val e.val.1.1 e.val.1.2=e.val := by
  obtain ⟨i,hi,j,hj,he⟩ := (query_member g.val k e.val).mp (List.mem_toFinset.mp e.property)
  rw [← he]
  exact ⟨hi,hj,rfl⟩

/-- Both directions are explicit indices from ACTUAL emitted edge records.
The physical compiler below never serializes a Fintype equivalence.
-/
def edgeEquiv (g : Input) (k : ℕ) : Copies g k ≃ UnitEdges (query g k) where
  toFun p := ⟨copyEdge g.val p.1.val p.2.val,List.mem_toFinset.mpr
    (query_occurrence g k p.1.val p.2.val p.1.isLt (by rw [← copies_eq]; exact p.2.isLt))⟩
  invFun e :=
    ⟨⟨e.val.1.1,(unit_edge_spec g k e).1⟩,
      ⟨e.val.1.2,by rw [copies_eq]; exact (unit_edge_spec g k e).2.1⟩⟩
  left_inv := by rintro ⟨i,j⟩; rfl
  right_inv := by
    intro e
    exact Subtype.ext ((unit_edge_spec g k e).2.2)

theorem edgeEquiv_endpoints (g : Input) (k : ℕ) (p : Copies g k) :
    (edgeEquiv g k p).val.2=(originalEdge g p.1).1 := by
  simp only [edgeEquiv,Equiv.coe_fn_mk,copyEdge,originalEdge,
    List.getD_eq_getElem _ _ p.1.isLt,List.get_eq_getElem]

theorem query_key_unique (g : Input) (k : ℕ) (e f : UnitEdges (query g k))
    (h : e.val.1=f.val.1) : e=f := by
  apply Subtype.ext
  calc
    e.val = copyEdge g.val e.val.1.1 e.val.1.2 := (unit_edge_spec g k e).2.2.symm
    _ = copyEdge g.val f.val.1.1 f.val.1.2 := by rw [h]
    _ = f.val := (unit_edge_spec g k f).2.2

/-- The copy label is retained independently for every selected occurrence.
No two parallel choices are identified with their equal endpoint pair.
-/
private def copyMatchingEquiv (g : Input) (k : ℕ) : UnitMatching (query g k) ≃
    {p : Fin g.val.1 → Copies g k //
      Perfect g.val.1 (fun e => (originalEdge g e).1.1) (fun e => (originalEdge g e).1.2)
        (fun r => (p r).1)} where
  toFun z :=
    let p := fun r : Fin g.val.1 => (edgeEquiv g k).symm (z.val r)
    ⟨p,by
      have he (r : Fin g.val.1) : (z.val r).val.2=(originalEdge g (p r).1).1 := by
        rw [← edgeEquiv_endpoints g k (p r),Equiv.apply_symm_apply]
      have hz := z.property
      change Perfect g.val.1 _ _ _ at hz
      simpa only [Perfect,← he] using hz⟩
  invFun z := ⟨fun r => edgeEquiv g k (z.val r),by
    change Perfect g.val.1 _ _ _
    simpa only [Perfect,edgeEquiv_endpoints] using z.property⟩
  left_inv := by
    intro z
    apply Subtype.ext
    funext r
    exact Equiv.apply_symm_apply _ _
  right_inv := by
    intro z
    apply Subtype.ext
    funext r
    exact Equiv.symm_apply_apply _ _

private def selections {R E : Type} (C : E → Type) (P : (R → E) → Prop) :
    {p : R → Sigma C // P (fun r => (p r).1)} ≃
      Σ m : {f : R → E // P f},∀ r,C (m.val r) where
  toFun z := ⟨⟨fun r => (z.val r).1,z.property⟩,fun r => (z.val r).2⟩
  invFun z := ⟨fun r => ⟨z.1.val r,z.2 r⟩,z.1.property⟩
  left_inv := by
    intro z
    apply Subtype.ext
    funext r
    cases z.val r
    rfl
  right_inv := by rintro ⟨⟨m,h⟩,c⟩; rfl

def matchingEquiv (g : Input) (k : ℕ) : UnitMatching (query g k) ≃
    Σ m : Matching g,∀ r : Fin g.val.1,Fin (copies g k (m.val r)) :=
  (copyMatchingEquiv g k).trans (selections (fun e => Fin (copies g k e))
    (Perfect g.val.1 (fun e => (originalEdge g e).1.1) (fun e => (originalEdge g e).1.2)))

def negativeCount (g : Input) (m : Matching g) : ℕ :=
  ∑ r : Fin g.val.1,if (originalEdge g (m.val r)).2 then 1 else 0
theorem negativeCount_le (g : Input) (m : Matching g) : negativeCount g m≤g.val.1 := by
  unfold negativeCount
  calc
    _ ≤ ∑ _r : Fin g.val.1,(1 : ℕ) := Finset.sum_le_sum (fun r _ => by split <;> omega)
    _ = _ := by simp

theorem copies_product (g : Input) (k : ℕ) (m : Matching g) :
    (∏ r : Fin g.val.1,copies g k (m.val r))=k^negativeCount g m := by
  have he (r : Fin g.val.1) : copies g k (m.val r)=
      k^(if (originalEdge g (m.val r)).2 then 1 else 0) := by
    cases h : (originalEdge g (m.val r)).2 <;> simp [copies,h]
  simp_rw [he]
  exact Finset.prod_pow_eq_pow_sum _ _ _

theorem query_count (g : Input) (k : ℕ) : unitCount (query g k)=
    ∑ m : Matching g,k^negativeCount g m := by
  rw [unitCount,Fintype.card_congr (matchingEquiv g k),Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro m _
  simpa only [Fintype.card_pi,Fintype.card_fin] using copies_product g k m

def polynomial (g : Input) : Polynomial ℚ := ∑ m : Matching g,Polynomial.X^negativeCount g m
def signedValue (g : Input) : ℚ := ∑ m : Matching g,(-1 : ℚ)^negativeCount g m
def unitValue (g : UnitInput) : ℚ := unitCount g

theorem polynomial_degree (g : Input) : (polynomial g).natDegree≤g.val.1 := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro m _
  exact (Polynomial.natDegree_X_pow_le _).trans (negativeCount_le g m)
theorem polynomial_sample (g : Input) (k : ℕ) : (polynomial g).eval (k : ℚ)=unitValue (query g k) := by
  simp only [polynomial,Polynomial.eval_finsetSum,Polynomial.eval_pow,Polynomial.eval_X,
    unitValue,query_count,Nat.cast_sum,Nat.cast_pow]
theorem polynomial_signed (g : Input) : (polynomial g).eval (-1)=signedValue g := by
  simp only [polynomial,signedValue,Polynomial.eval_finsetSum,Polynomial.eval_pow,Polynomial.eval_X]

def nodes (n : ℕ) (i : Fin (n+1)) : ℚ := i.val
def weight (n : ℕ) (i : Fin (n+1)) : ℚ := (Lagrange.basis Finset.univ (nodes n) i).eval (-1)
def recover (n : ℕ) (ys : List ℚ) : ℚ :=
  ∑ i : Fin (n+1),ys.getD i.val 0*weight n i
def queries (g : Input) : List UnitInput := (List.range (g.val.1+1)).map (query g)

theorem nodes_injective (n : ℕ) : Function.Injective (nodes n) := by
  intro i j h
  apply Fin.ext
  exact_mod_cast (show (i.val : ℚ)=j.val from h)

/-- n+1 shared-parameter queries recover p(-1); there is no per-occurrence
Cartesian expansion. The degree premise is produced from actual matchings.
-/
theorem recovery (g : Input) : recover g.val.1 ((queries g).map unitValue)=signedValue g := by
  have hd : (polynomial g).degree<(g.val.1+1 : ℕ) :=
    lt_of_le_of_lt Polynomial.degree_le_natDegree (by exact_mod_cast (Nat.lt_succ_of_le (polynomial_degree g)))
  have hi := Lagrange.eq_interpolate (s := Finset.univ) (f := polynomial g) (nodes_injective g.val.1).injOn
    (by simpa using hd)
  have he := congrArg (Polynomial.eval (-1 : ℚ)) hi
  unfold recover
  calc
    _ = ∑ i : Fin (g.val.1+1),(polynomial g).eval (nodes g.val.1 i)*weight g.val.1 i := by
      apply Finset.sum_congr rfl
      intro i _
      have hl : i.val<(queries g).length := by simpa only [queries,List.length_map,List.length_range] using i.isLt
      have hm : i.val<((queries g).map unitValue).length := by simpa only [List.length_map] using hl
      rw [List.getD_eq_getElem _ _ hm]
      simp only [queries,List.getElem_map,List.getElem_range,nodes,polynomial_sample]
    _ = (polynomial g).eval (-1) := by simpa [Lagrange.interpolate_apply,Polynomial.eval_finsetSum,
      Polynomial.eval_mul,Polynomial.eval_C,weight] using he.symm
    _ = _ := polynomial_signed g

theorem number_queries (g : Input) : (queries g).length=g.val.1+1 := by simp [queries]

theorem input_counts (g : Input) :
    g.val.1≤(encoding.encode g).length ∧ g.val.2.length≤(encoding.encode g).length := by
  have h := framedListEncoding_length_lower edgeEncoding g.val.2
  simp only [encoding,rawEncoding,pairEncoding_length,UnaryBinary.unaryEncoding,List.length_replicate]
  omega

theorem copies_le (g : Input) (k : ℕ) (e : OriginalEdges g) : copies g k e≤k+1 := by
  unfold copies
  split <;> omega

theorem copied_edge_count (g : Input) (k : ℕ) :
    Fintype.card (UnitEdges (query g k))≤g.val.2.length*(k+1) := by
  rw [← Fintype.card_congr (edgeEquiv g k),Fintype.card_sigma]
  simp only [Fintype.card_fin]
  calc
    _ ≤ ∑ _e : OriginalEdges g,(k+1) := Finset.sum_le_sum (fun e _ => copies_le g k e)
    _ = _ := by simp

private theorem nat_le_two_pow (a : ℕ) : a≤2^a := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [pow_succ]
    have h : 1≤2^a := Nat.one_le_two_pow
    omega

/-- Counting uses the ACTUAL query edge IDs, not just the endpoint graph.
This bounds the logarithm of its answer without assuming a matching count.
-/
theorem answer_count_bound (g : Input) (k : ℕ) :
    unitCount (query g k)≤2^(g.val.1*g.val.2.length*(k+1)) := by
  classical
  have h := Fintype.card_subtype_le
    (Perfect g.val.1 (fun e : UnitEdges (query g k) => e.val.2.1)
      (fun e => e.val.2.2))
  change unitCount (query g k)≤Fintype.card (Fin g.val.1 → UnitEdges (query g k)) at h
  simp only [Fintype.card_fun,Fintype.card_fin] at h
  calc
    _ ≤ (g.val.2.length*(k+1))^g.val.1 :=
      h.trans (Nat.pow_le_pow_left (copied_edge_count g k) _)
    _ ≤ (2^(g.val.2.length*(k+1)))^g.val.1 :=
      Nat.pow_le_pow_left (nat_le_two_pow _) _
    _ = _ := by rw [← pow_mul]; congr 1; ring

def answerBudget : Polynomial ℕ := Polynomial.X*Polynomial.X*(Polynomial.X+1)
theorem sample_count_bound (g : Input) (i : Fin (g.val.1+1)) :
    unitCount (query g i.val)≤2^(answerBudget.eval (encoding.encode g).length) := by
  have hn := (input_counts g).1
  have hm := (input_counts g).2
  have hi : i.val≤g.val.1 := by omega
  apply (answer_count_bound g i.val).trans
  apply Nat.pow_le_pow_right (by decide)
  simp only [answerBudget,Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
  exact Nat.mul_le_mul (Nat.mul_le_mul hn hm) (Nat.add_le_add_right (hi.trans hn) 1)

def signedWeight (g : Input) (m : Matching g) : ℚ :=
  ∏ r : Fin g.val.1,if (originalEdge g (m.val r)).2 then -1 else 1
theorem signedWeight_eq (g : Input) (m : Matching g) : signedWeight g m=(-1 : ℚ)^negativeCount g m := by
  have he (r : Fin g.val.1) : (if (originalEdge g (m.val r)).2 then (-1 : ℚ) else 1)=
      (-1 : ℚ)^(if (originalEdge g (m.val r)).2 then 1 else 0) := by
    cases h : (originalEdge g (m.val r)).2 <;> simp [h]
  simp only [signedWeight]
  simp_rw [he]
  exact Finset.prod_pow_eq_pow_sum _ _ _
theorem original_signed_partition (g : Input) : (∑ m : Matching g,signedWeight g m)=signedValue g := by
  simp only [signedWeight_eq,signedValue]

def integerValue (g : Input) : ℤ := ∑ m : Matching g,(-1 : ℤ)^negativeCount g m
theorem signed_integer (g : Input) : (integerValue g : ℚ)=signedValue g := by
  simp [integerValue,signedValue]

theorem matching_injective (g : Input) (m : Matching g) : Function.Injective m.val := by
  intro r s h
  apply Fin.ext
  exact (m.property.1 r).symm.trans
    ((congrArg (fun e => (originalEdge g e).1.1) h).trans (m.property.1 s))

theorem empty_count (g : UnitInput) (h : g.val.1=0) : unitCount g=1 := by
  rcases g with ⟨⟨n,es⟩,hg⟩
  change n=0 at h
  subst n
  simp [unitCount,UnitMatching,Perfect]

theorem unit_input_counts (g : UnitInput) :
    g.val.1≤(unitEncoding.encode g).length ∧ g.val.2.length≤(unitEncoding.encode g).length := by
  have h := framedListEncoding_length_lower unitEdgeEncoding g.val.2
  simp only [unitEncoding,unitRawEncoding,pairEncoding_length,UnaryBinary.unaryEncoding,List.length_replicate]
  omega

theorem unit_answer_bound (g : UnitInput) :
    unitCount g≤2^((unitEncoding.encode g).length^2) := by
  have h := Fintype.card_subtype_le
    (Perfect g.val.1 (fun e : UnitEdges g => e.val.2.1) (fun e => e.val.2.2))
  change unitCount g≤Fintype.card (Fin g.val.1 → UnitEdges g) at h
  simp only [Fintype.card_fun,Fintype.card_fin] at h
  have he : Fintype.card (UnitEdges g)=g.val.2.length := by
    simp only [UnitEdges,Fintype.card_coe,List.toFinset_card_of_nodup g.property.1]
  rw [he] at h
  have hn := (unit_input_counts g).1
  have hm := (unit_input_counts g).2
  calc
    _ ≤ (2^g.val.2.length)^g.val.1 := h.trans (Nat.pow_le_pow_left (nat_le_two_pow _) _)
    _ = 2^(g.val.2.length*g.val.1) := by rw [← pow_mul]
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by simpa [pow_two] using Nat.mul_le_mul hm hn)

end
end Holant.LocalDrafts.Hardness.EightVertexNonexception.SixVertexInterpolation.VerifierGates.WeightedMatchingInterpolation
