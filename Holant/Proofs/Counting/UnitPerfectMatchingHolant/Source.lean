import Holant.Proofs.Counting.UnitPerfectMatchingHolant.Compiler
import Holant.Complexity.FixedFieldMachines.Constant
import Holant.Complexity.FixedGadgetSubstitution.TemplateSemantics
import Holant.Complexity.FixedGadgetSubstitution.Partition
import Holant.OrdinaryNetwork
import Holant.Proofs.Counting.UnitPerfectMatchingHolant.Programs


noncomputable section
namespace Holant.LocalDrafts.CountingHardness.UnitPerfectMatchingHolant.Source
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
open Turing Computability Holant Holant.Algebraic Holant.Complexity
open GraphPreprocessing
open FixedFieldMachines BinaryCompose
open FixedGadgetSubstitution
open scoped BigOperators
open Holant.LocalDrafts.Hardness.EightVertexNonexception.SixVertexInterpolation.VerifierGates.WeightedMatchingInterpolation

abbrev TargetInput := {r : RawClosedNetwork // r.WellFormed 3 1 Tree.arity}
def targetEncoding := RawClosedNetwork.validatedEncoding 3 1 Tree.arity
def targetValue (r : TargetInput) : ℚ :=
  (r.val.realize r.property Tree.alphabet Tree.edge).denote Fin.elim0

namespace Literal
def extend {n : ℕ} (c : Fin n → Bool) (i : ℕ) : Bool :=
  if h : i<n then c ⟨i,h⟩ else false
def slot (w : List Bool) (c : ℕ → Bool) : LocalEndpoint → Bool
  | .inl i => w.getD i false
  | .inr p => c p.1
def gate (tag : ℕ) (x : ℕ → Bool) : ℚ := match tag with
  | 0 => Tree.ternary (fun i => x i.val)
  | 1 => Tree.binaryX (fun i => x i.val)
  | _ => Tree.pin1 (fun i => x i.val)
def rowWeight (w : List Bool) (c : ℕ → Bool) (row : LocalVertex) : ℚ :=
  gate row.1 (fun i => slot w c (row.2.getD i (.inl 0)))
def rowsWeight (w : List Bool) (c : ℕ → Bool) (rows : List LocalVertex) : ℚ :=
  (rows.map (rowWeight w c)).prod

theorem gate_table (i : Fin 3) (a : ℕ → Bool) :
    gate i.val a=Tree.alphabet i (fun j => a j.val) := by
  fin_cases i <;> rfl
theorem extend_at {n : ℕ} (c : Fin n → Bool) (i : Fin n) : extend c i.val=c i := by
  simp [extend,i.isLt]
theorem extend_cast {n m : ℕ} (h : n=m) (c : Fin n → Bool) :
    extend c=extend (fun j : Fin m => c (Fin.cast h.symm j)) := by
  cases h
  rfl
theorem slot_embed {n e : ℕ} (x : Fin n → Bool) (c : Fin e → Bool)
    (p : Fin n ⊕ (Fin e × Bool)) :
    slot (List.ofFn x) (extend c) (Template.embed n e p)=
      Sum.elim x (fun q => c q.1) p := by
  cases p with
  | inl i =>
      simp only [Template.embed,Sum.elim_inl,slot]
      rw [List.getD_eq_getElem _ _ (by simpa using i.isLt)]
      simp
  | inr p => exact extend_at c p.1

/-- Actual stored ordered port, via the old validator's route receipt. -/
theorem assigned_port (T : Template) (hT : T.WellFormed 3 1 Tree.arity)
    (x : Fin T.boundary → Bool) (c : Fin T.edges.length → Bool)
    (v : Fin T.vertices.length) (i : Fin (Tree.arity (T.vertices.get v).1)) :
    (T.network hT Tree.alphabet Tree.edge).shape.assignment x (fun p => c p.1) v i =
      slot (List.ofFn x) (extend c) ((T.vertices.get v).2.getD i.val (.inl 0)) := by
  change Sum.elim x (fun p => c p.1) (T.route hT ⟨v,i⟩)=_
  rw [←slot_embed x c (T.route hT ⟨v,i⟩),Template.embed_route]
  unfold Template.portEndpoint
  have hi : i.val<(T.vertices.get v).2.length := by
    rw [(hT.1 _ (List.get_mem _ v)).2]
    exact i.isLt
  rw [List.getD_eq_getElem _ _ hi,List.get_eq_getElem]
  rfl

/-- Existing ordinary equality compression is applied to this exact template;
the endpoint decoder, rather than a new incidence map, supplies every bit. -/
theorem template_rows (T : Template) (hT : T.WellFormed 3 1 Tree.arity)
    (x : Fin T.boundary → Bool) :
    (T.network hT Tree.alphabet Tree.edge).denote x =
      ∑ c : Fin T.edges.length → Bool,rowsWeight (List.ofFn x) (extend c) T.vertices := by
  change (Network.mk (T.network hT Tree.alphabet Tree.edge).shape
    (T.network hT Tree.alphabet Tree.edge).vertex (fun _ => Signature.equality)).denote x=_
  rw [Network.denote_equality]
  unfold Network.ordinaryDenote
  apply Finset.sum_congr rfl
  intro c _
  change Fin T.edges.length → Bool at c
  unfold rowsWeight
  rw [←List.ofFn_getElem_eq_map T.vertices (rowWeight (List.ofFn x) (extend c)),List.prod_ofFn]
  apply Finset.prod_congr rfl
  intro v _
  change Fin T.vertices.length at v
  unfold rowWeight
  change (T.network hT Tree.alphabet Tree.edge).vertex v
    ((T.network hT Tree.alphabet Tree.edge).shape.assignment x (fun p=>c p.1) v)=
      gate (T.vertices.get v).1 (fun i=>slot (List.ofFn x) (extend c) ((T.vertices.get v).2.getD i (.inl 0)))
  rw [gate_table ⟨(T.vertices.get v).1,(hT.1 _ (List.get_mem _ v)).1⟩]
  apply congrArg (Tree.alphabet ⟨(T.vertices.get v).1,(hT.1 _ (List.get_mem _ v)).1⟩)
  funext i
  exact assigned_port T hT x c v i

theorem slot_moved (m : ℕ) (w : List Bool) (c : ℕ → Bool) (p : LocalEndpoint) :
    slot w c (Tree.moved m p)=slot (c (2*m)::w.drop 2) c p := by
  cases p with
  | inl i =>
      cases i with
      | zero => rfl
      | succ i =>
          cases w with
          | nil => rfl
          | cons a w => cases w <;> rfl
  | inr p => rfl

theorem row_moved (m : ℕ) (w : List Bool) (c : ℕ → Bool) (row : LocalVertex)
    (hl : row.1<3) (ha : row.2.length=Tree.arity row.1) :
    rowWeight w c (row.1,row.2.map (Tree.moved m))=
      rowWeight (c (2*m)::w.drop 2) c row := by
  unfold rowWeight
  rw [gate_table ⟨row.1,hl⟩,gate_table ⟨row.1,hl⟩]
  congr 1
  funext i
  have hi : i.val<row.2.length := by rw [ha]; exact i.isLt
  rw [List.getD_eq_getElem _ _ (by simpa using hi),List.getD_eq_getElem _ _ hi]
  simp only [List.getElem_map]
  exact slot_moved m w c _

def internalWord : ℕ → (ℕ → Bool) → List Tree.Wire
  | 0,_ => []
  | m+1,c => (c (2*m+1),c (2*m))::internalWord m c
theorem internalWord_length (m : ℕ) (c : ℕ → Bool) : (internalWord m c).length=m := by
  induction m <;> simp [internalWord, *]
theorem internalWord_congr (m : ℕ) (c d : ℕ → Bool)
    (h : ∀ i<2*m,c i=d i) : internalWord m c=internalWord m d := by
  induction m with
  | zero => rfl
  | succ m ih =>
      simp only [internalWord]
      rw [h (2*m+1) (by omega),h (2*m) (by omega),ih (fun i hi => h i (by omega))]

/-- The exact literal row product follows the old template's chronological
edge IDs. Only the local assignment WORD is read in reverse chain order. -/
theorem tree_rows (m : ℕ) (w : List Bool) (hw : w.length=m+3) (c : ℕ → Bool) :
    rowsWeight w c (Tree.template m).vertices=Tree.weight w (internalWord m c) := by
  classical
  induction m generalizing w with
  | zero =>
      cases w with
      | nil => simp at hw
      | cons a w =>
          cases w with
          | nil => simp at hw
          | cons b w =>
              cases w with
              | nil => simp at hw
              | cons d tail =>
                  have ht : tail=[] := List.eq_nil_of_length_eq_zero (by simp only [List.length_cons] at hw; omega)
                  subst tail
                  cases a <;> cases b <;> cases d <;>
                    simp [rowsWeight,rowWeight,slot,gate,Tree.template,Tree.ternary,
                      Tree.tri,Tree.bit,Tree.weight,internalWord]
  | succ m ih =>
      cases w with
      | nil => simp at hw
      | cons a w =>
          cases w with
          | nil => simp at hw
          | cons b tail =>
              have hm : (c (2*m)::tail).length=m+3 := by
                simp only [List.length_cons] at hw ⊢
                omega
              have hr : rowsWeight (a::b::tail) c
                  ((Tree.template m).vertices.map (fun row => (row.1,row.2.map (Tree.moved m)))) =
                  rowsWeight (c (2*m)::tail) c (Tree.template m).vertices := by
                unfold rowsWeight
                simp only [List.map_map]
                apply congrArg List.prod
                apply List.map_congr_left
                intro row hrow
                have hl := Tree.template_labels m row hrow
                simpa using row_moved m (a::b::tail) c row hl.1 hl.2
              simp only [Tree.template,rowsWeight,List.map_append,List.prod_append]
              change rowsWeight (a::b::tail) c
                ((Tree.template m).vertices.map (fun row => (row.1,row.2.map (Tree.moved m)))) *
                (([(1,[.inr (2*m,true),.inr (2*m+1,false)]),
                  (0,[.inl 0,.inl 1,.inr (2*m+1,true)])]).map (rowWeight (a::b::tail) c)).prod=_
              rw [hr,ih _ hm]
              have hbin : rowWeight (a::b::tail) c
                  (1,[.inr (2*m,true),.inr (2*m+1,false)])=
                  Signature.disequality (c (2*m)) (c (2*m+1)) := rfl
              have htri : rowWeight (a::b::tail) c
                  (0,[.inl 0,.inl 1,.inr (2*m+1,true)])=
                  (if Tree.tri a b (c (2*m+1)) then 1 else 0) := rfl
              simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,hbin,htri,mul_one,
                internalWord,Tree.weight]
              by_cases h : Tree.tri a b (c (2*m+1)) <;> simp only [h,ite_true,ite_false,mul_zero] <;> ring

def pairEnd (m : ℕ) (i : Fin m) (odd : Bool) : Fin (2*m) :=
  ⟨2*(m-1-i.val)+(if odd then 1 else 0),by
    have hi := i.isLt
    cases odd <;> simp only [Bool.false_eq_true,if_false,if_true] <;> omega⟩
def packing (m : ℕ) (c : Fin (2*m) → Bool) : Fin m → Tree.Wire :=
  fun i => (c (pairEnd m i true),c (pairEnd m i false))
def pairRow (m : ℕ) (j : Fin (2*m)) : Fin m :=
  ⟨m-1-j.val/2,by have hj := j.isLt; omega⟩
def unpacking (m : ℕ) (f : Fin m → Tree.Wire) : Fin (2*m) → Bool :=
  fun j => if j.val%2=0 then (f (pairRow m j)).2 else (f (pairRow m j)).1

/-- Concrete even/odd original edge slots, reversed into recurrence order.
Both inverse proofs are ordinary exact natural-number coordinate proofs. -/
def packingEquiv (m : ℕ) : (Fin (2*m) → Bool) ≃ (Fin m → Tree.Wire) where
  toFun := packing m
  invFun := unpacking m
  left_inv := by
    intro c
    funext j
    have hj := j.isLt
    by_cases he : j.val%2=0
    · have hp : pairEnd m (pairRow m j) false=j := by
        apply Fin.ext
        simp only [pairEnd,pairRow,Bool.false_eq_true,if_false]
        omega
      simp only [unpacking,if_pos he,packing]
      rw [hp]
    · have hp : pairEnd m (pairRow m j) true=j := by
        apply Fin.ext
        simp only [pairEnd,pairRow,if_true]
        omega
      simp only [unpacking,if_neg he,packing]
      rw [hp]
  right_inv := by
    intro f
    funext i
    have hi := i.isLt
    have h0 : (pairEnd m i false).val%2=0 := by
      simp only [pairEnd,Bool.false_eq_true,if_false]
      omega
    have h1 : (pairEnd m i true).val%2≠0 := by
      simp only [pairEnd,if_true]
      omega
    have hp (b : Bool) : pairRow m (pairEnd m i b)=i := by
      apply Fin.ext
      cases b <;> simp only [pairRow,pairEnd,Bool.false_eq_true,if_false,if_true] <;> omega
    apply Prod.ext
    · simp only [packing,unpacking,if_neg h1,hp true]
    · simp only [packing,unpacking,if_pos h0,hp false]

theorem packing_word (m : ℕ) (c : Fin (2*m) → Bool) :
    List.ofFn (packing m c)=internalWord m (extend c) := by
  induction m with
  | zero => simp [internalWord]
  | succ m ih =>
      let old : Fin (2*m) → Bool := fun j => c ⟨j.val,by have hj := j.isLt; omega⟩
      have ht : (fun i : Fin m => packing (m+1) c i.succ)=packing m old := by
        funext i
        have hi := i.isLt
        apply Prod.ext
        all_goals
          apply congrArg c
          apply Fin.ext
          simp [packing,pairEnd,old] <;> omega
      have hhead : packing (m+1) c 0=(extend c (2*m+1),extend c (2*m)) := by
        have h0 : 2*m<2*(m+1) := by omega
        have h1 : 2*m+1<2*(m+1) := by omega
        apply Prod.ext <;> simp [packing,pairEnd,extend,h0,h1]
      rw [List.ofFn_succ,ht,hhead,ih old,internalWord]
      apply congrArg (List.cons (extend c (2*m+1),extend c (2*m)))
      apply internalWord_congr
      intro j hj
      have hj' : j<2*(m+1) := by omega
      simp [extend,hj,hj',old]

/-- Every validated tree denotes its actual packed cell partition. This
closes the former first mathematical gap with no denotation premise. -/
theorem tree_denote (m : ℕ) (x : Fin (Tree.template m).boundary → Bool) :
    ((Tree.template m).network (Tree.template_wellFormed m) Tree.alphabet Tree.edge).denote x =
      Tree.localPartition m (List.ofFn x) := by
  rw [template_rows]
  have hb : (List.ofFn x).length=m+3 := by
    simpa using (Tree.template_counts m).1
  have he := (Tree.template_counts m).2.2
  let e : (Fin (Tree.template m).edges.length → Bool) ≃ (Fin (2*m) → Bool) :=
    Equiv.arrowCongr (finCongr he) (Equiv.refl Bool)
  have hw (c : Fin (Tree.template m).edges.length → Bool) :
      internalWord m (extend c)=internalWord m (extend (e c)) := by
    apply internalWord_congr
    intro j hj
    have hj' : j<(Tree.template m).edges.length := by omega
    simp only [extend,dif_pos hj,dif_pos hj']
    change c ⟨j,hj'⟩=c (Fin.cast he.symm ⟨j,hj⟩)
    rfl
  simp_rw [tree_rows m _ hb]
  have hsum : (∑ c : Fin (Tree.template m).edges.length → Bool,
      Tree.weight (List.ofFn x) (internalWord m (extend c))) =
      ∑ c : Fin (2*m) → Bool,Tree.weight (List.ofFn x) (List.ofFn (packing m c)) := by
    apply Fintype.sum_equiv e
    intro c
    rw [packing_word,hw]
  rw [hsum]
  exact (packingEquiv m).sum_comp (fun f => Tree.weight (List.ofFn x) (List.ofFn f))

theorem tree_exact (m : ℕ) (x : Fin (Tree.template m).boundary → Bool) :
    ((Tree.template m).network (Tree.template_wellFormed m) Tree.alphabet Tree.edge).denote x =
      if (List.ofFn x).count true=1 then 1 else 0 := by
  rw [tree_denote,Tree.local_partition_exact m _ (by simpa using (Tree.template_counts m).1)]

end Literal

/-- The degree-zero local placeholder denotes ONE. It is kept explicit
and never confused with exact-one-zero; the actual zeroTest branch does
not query it. Every positive-degree row has the true exact-one tensor. -/
def localSource (d : ℕ) : Signature ℚ (Compiler.degreeTemplate d).boundary :=
  if d=0 then fun _ => 1
  else fun x => if (List.ofFn x).count true=1 then 1 else 0

theorem degree_denote (d : ℕ) :
    ((Compiler.degreeTemplate d).network (Compiler.degree_valid d) Tree.alphabet Tree.edge).denote=
      localSource d := by
  rcases d with _ | _ | _ | m
  · funext x
    rw [Literal.template_rows]
    simp [Compiler.degreeTemplate,localSource,Literal.rowsWeight]
  · funext x
    rw [Literal.template_rows]
    change Fin 1 → Bool at x
    cases h : x 0 <;>
      simp [Compiler.degreeTemplate,localSource,Literal.rowsWeight,Literal.rowWeight,
        Literal.slot,Literal.gate,Tree.pin1,List.ofFn_succ,h]
  · funext x
    rw [Literal.template_rows]
    change Fin 2 → Bool at x
    cases h0 : x 0 <;> cases h1 : x 1 <;>
      simp [Compiler.degreeTemplate,localSource,Literal.rowsWeight,Literal.rowWeight,
        Literal.slot,Literal.gate,Tree.binaryX,Signature.disequality,List.ofFn_succ,h0,h1]
  · funext x
    simpa [Compiler.degreeTemplate,localSource] using Literal.tree_exact m x

def virtualSourceValid (g : UnitInput) :
    (Compiler.virtual g).WellFormed (g.val.2.length+1) 1
      (sourceArity Compiler.degreeTemplate) := by
  have ha : sourceArity Compiler.degreeTemplate=id := by
    funext d
    exact Compiler.degree_boundary d
  simpa only [ha] using Compiler.virtual_valid g
def virtualValue (g : UnitInput) : ℚ :=
  ((Compiler.virtual g).realize (virtualSourceValid g)
    (fun i => localSource i.val) Tree.edge).denote Fin.elim0

/-- Actual whole raw physical substitution, not a conclusion-shaped local
denotation premise. All local tensors come from degree_denote above. -/
theorem query_to_virtual (g : UnitInput) : targetValue (Compiler.query g)=virtualValue g := by
  have h := replacement_partition Compiler.degreeTemplate (Compiler.virtual g)
    (virtualSourceValid g) (fun d _ => Compiler.degree_valid d)
    (fun i => localSource i.val) Tree.alphabet Tree.edge (fun _ => (1 : ℚ))
    (fun i => by simpa using degree_denote i.val)
  simpa [targetValue,Compiler.query,Compiler.queryRaw,virtualValue] using h

namespace Occurrence
attribute [local instance] Classical.propDecidable
def coordinate {g : UnitInput} (b : Bool) (e : UnitEdges g) : ℕ :=
  if b then e.val.2.2 else e.val.2.1
def allEdges (g : UnitInput) : List (UnitEdges g) := List.ofFn (Compiler.occurrence g)
def incident (g : UnitInput) (b : Bool) (r : ℕ) : List (UnitEdges g) :=
  (allEdges g).filter (fun e => decide (coordinate b e=r))
def bits (g : UnitInput) (c : Fin g.val.2.length → Bool) : Incidence.Selection g :=
  fun e => c ((Compiler.occurrenceEquiv g).symm e)
def portWord (g : UnitInput) (b : Bool) (r : ℕ) (c : Fin g.val.2.length → Bool) : List Bool :=
  (Compiler.ports g b r).map (fun p => Literal.extend c p.1)

theorem allEdges_mem (g : UnitInput) (e : UnitEdges g) : e∈allEdges g :=
  List.mem_ofFn.mpr (Compiler.occurrence_surjective g e)
theorem incident_mem (g : UnitInput) (b : Bool) (r : ℕ) (e : UnitEdges g) :
    e∈incident g b r ↔ coordinate b e=r := by
  simp [incident,allEdges_mem,decide_eq_true_eq]
theorem incident_nodup (g : UnitInput) (b : Bool) (r : ℕ) : (incident g b r).Nodup :=
  (List.nodup_ofFn_ofInjective (Compiler.occurrence_injective g)).filter _

private theorem filtered_word {A B : Type} (xs : List A) (p : A → Bool) (f : A → B) :
    (xs.filter p).map f=xs.flatMap (fun a => if p a then [f a] else []) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => cases h : p a <;> simp [h,ih]

theorem portWord_exact (g : UnitInput) (b : Bool) (r : ℕ) (c : Fin g.val.2.length → Bool) :
    portWord g b r c=(incident g b r).map (bits g c) := by
  unfold portWord Compiler.ports incident allEdges
  rw [filtered_word,List.ofFn_eq_map,←List.map_coe_finRange_eq_range]
  simp only [List.map_flatMap,List.flatMap_map]
  congr 1
  funext i
  have he := Compiler.endpoint_occurrence g b i
  have hz : bits g c (Compiler.occurrence g i)=c i := by
    change c ((Compiler.occurrenceEquiv g).symm ((Compiler.occurrenceEquiv g) i))=c i
    rw [Equiv.symm_apply_apply]
  rw [he]
  by_cases h : coordinate b (Compiler.occurrence g i)=r
  all_goals simp only [coordinate] at h
  all_goals simp [coordinate,h,hz,Literal.extend_at,decide_eq_true_eq]

private theorem count_one {A : Type} [DecidableEq A] (xs : List A) (f : A → Bool)
    (hx : xs.Nodup) :
    (xs.map f).count true=1 ↔ ∃! a,a∈xs ∧ f a=true := by
  have hc : (xs.map f).count true=(xs.filter f).length := by
    clear hx
    induction xs with
    | nil=>rfl
    | cons a xs ih=>cases h : f a <;> simp [h,ih]
  rw [hc]
  constructor
  · intro h
    obtain ⟨a,ha⟩ := List.length_eq_one_iff.mp h
    have hm : a∈xs.filter f := by rw [ha]; simp
    refine ⟨a,List.mem_filter.mp hm,?_⟩
    intro b hb
    have hm' : b∈xs.filter f := List.mem_filter.mpr hb
    rw [ha] at hm'
    exact List.mem_singleton.mp hm'
  · rintro ⟨a,ha,hu⟩
    have hs : (xs.filter f).toFinset={a} := by
      ext b
      simp only [List.mem_toFinset,Finset.mem_singleton]
      constructor
      · intro hb
        exact hu b (List.mem_filter.mp hb)
      · intro hb
        subst b
        exact List.mem_filter.mpr ha
    rw [←List.toFinset_card_of_nodup (hx.filter f),hs]
    simp

theorem portWord_one (g : UnitInput) (b : Bool) (r : ℕ) (c : Fin g.val.2.length → Bool) :
    (portWord g b r c).count true=1 ↔
      ∃! e : UnitEdges g,coordinate b e=r ∧ bits g c e=true := by
  rw [portWord_exact,count_one _ _ (incident_nodup g b r)]
  simp_rw [incident_mem]

/-- Whole original row/column support, including every parallel occurrence,
is exactly the predicate consumed by the delivered matching bijection. -/
theorem support_iff (g : UnitInput) (c : Fin g.val.2.length → Bool) :
    (∀ p∈Compiler.nodes g,(portWord g p.1 p.2 c).count true=1) ↔
      Incidence.Selected g (bits g c) := by
  constructor
  · intro h
    constructor
    · intro r
      simpa only [coordinate,Bool.false_eq_true,if_false] using
        (portWord_one g false r.val c).mp (h (false,r.val) (by simp [Compiler.nodes,r.isLt]))
    · intro r
      simpa only [coordinate,if_true] using
        (portWord_one g true r.val c).mp (h (true,r.val) (by simp [Compiler.nodes,r.isLt]))
  · intro h p hp
    change p∈(List.range g.val.1).map (false,·) ++ (List.range g.val.1).map (true,·) at hp
    rcases List.mem_append.mp hp with hr | hc
    · obtain ⟨r,hrange,rfl⟩ := List.mem_map.mp hr
      apply (portWord_one g false r c).mpr
      exact h.1 ⟨r,List.mem_range.mp hrange⟩
    · obtain ⟨r,hrange,rfl⟩ := List.mem_map.mp hc
      apply (portWord_one g true r c).mpr
      exact h.2 ⟨r,List.mem_range.mp hrange⟩

theorem nonzero_degree (g : UnitInput) (h : Compiler.zeroTest g=false)
    (p : Bool × ℕ) (hp : p∈Compiler.nodes g) : (Compiler.ports g p.1 p.2).length≠0 := by
  intro hz
  have he : Compiler.ports g p.1 p.2=[] := List.eq_nil_of_length_eq_zero hz
  have ht : Compiler.zeroTest g=true := List.any_eq_true.mpr ⟨p,hp,by simp [he]⟩
  rw [h] at ht
  cases ht

theorem list_product_indicator {A : Type} (xs : List A) (p : A → Prop) [DecidablePred p] :
    (xs.map (fun a => if p a then (1 : ℚ) else 0)).prod=
      if ∀ a∈xs,p a then 1 else 0 := by
  induction xs with
  | nil => simp
  | cons a xs ih => by_cases ha : p a <;> by_cases ht : ∀ b∈xs,p b <;> simp [ha,ht,ih]

end Occurrence

namespace Closed
attribute [local instance] Classical.propDecidable

/-- Whole word at a vertex of the OLD faithful decoder, in precisely the
stored port order. Both ends of a loop remain distinct occurrences. -/
theorem word (r : RawClosedNetwork) {s b : ℕ} {a : ℕ → ℕ}
    (hr : r.WellFormed s b a) (c : Fin r.edges.length → Bool) (v : Fin r.vertices.length) :
    List.ofFn ((r.shape hr).assignment Fin.elim0 (fun p => c p.1) v) =
      (r.vertices.get v).2.map (fun p => Literal.extend c p.1) := by
  apply List.ext_getElem
  · simpa only [List.length_ofFn,List.length_map,RawClosedNetwork.shape] using (hr.1 v).2.symm
  · intro i hi hj
    have hb : i<a (r.vertices.get v).1 := by simpa only [List.length_ofFn,RawClosedNetwork.shape] using hi
    have hport : i<(r.vertices.get v).2.length := by rw [(hr.1 v).2]; exact hb
    rw [List.getElem_ofFn,List.getElem_map]
    change c (r.route hr ⟨v,⟨i,hb⟩⟩).1=
      Literal.extend c ((r.vertices.get v).2[i]).1
    have he : ((r.vertices.get v).2[i]).1=(r.route hr ⟨v,⟨i,hb⟩⟩).1.val := by
      rfl
    rw [he]
    exact (Literal.extend_at c (r.route hr ⟨v,⟨i,hb⟩⟩).1).symm

theorem virtual_rows (g : UnitInput) : virtualValue g =
    ∑ c : Fin (Compiler.virtual g).edges.length → Bool,
      (((Compiler.virtual g).vertices.map (fun row =>
        if row.1=0 then (1 : ℚ)
        else if (row.2.map (fun p => Literal.extend c p.1)).count true=1 then 1 else 0)).prod) := by
  unfold virtualValue
  change (Network.mk ((Compiler.virtual g).shape (virtualSourceValid g))
    (fun v => localSource ((Compiler.virtual g).signatureLabel (virtualSourceValid g) v).val)
    (fun _ => Signature.equality)).denote Fin.elim0=_
  rw [Network.denote_equality]
  unfold Network.ordinaryDenote
  apply Finset.sum_congr rfl
  intro c _
  change Fin (Compiler.virtual g).edges.length → Bool at c
  rw [←List.ofFn_getElem_eq_map (Compiler.virtual g).vertices
    (fun row => if row.1=0 then (1 : ℚ)
      else if (row.2.map (fun p => Literal.extend c p.1)).count true=1 then 1 else 0),
    List.prod_ofFn]
  apply Finset.prod_congr rfl
  intro v _
  change Fin (Compiler.virtual g).vertices.length at v
  change localSource ((Compiler.virtual g).vertices.get v).1
    (((Compiler.virtual g).shape (virtualSourceValid g)).assignment Fin.elim0 (fun p=>c p.1) v)=
    if ((Compiler.virtual g).vertices.get v).1=0 then (1 : ℚ) else
      if (((Compiler.virtual g).vertices.get v).2.map (fun p=>Literal.extend c p.1)).count true=1 then 1 else 0
  by_cases hd : ((Compiler.virtual g).vertices.get v).1=0
  · simp only [localSource,hd,ite_true]
  · simp only [localSource,hd,ite_false]
    rw [word (Compiler.virtual g) (virtualSourceValid g) c v]

/-- The true finite global value follows from the actual ordered words and
the previously delivered occurrence matching bijection. The nonzero-test
condition is generated by Source.top/Programs.zero, not a count premise. -/
theorem virtual_count (g : UnitInput) (hz : Compiler.zeroTest g=false) :
    virtualValue g=unitValue g := by
  rw [virtual_rows]
  have he : (Compiler.virtual g).edges.length=g.val.2.length := by simp [Compiler.virtual]
  let e : (Fin (Compiler.virtual g).edges.length → Bool) ≃ Incidence.Selection g :=
    Equiv.arrowCongr ((finCongr he).trans (Compiler.occurrenceEquiv g)) (Equiv.refl Bool)
  change _=(unitCount g : ℚ)
  rw [←Incidence.partition_count g]
  unfold Incidence.partition
  apply Fintype.sum_equiv e
  intro c
  let old : Fin g.val.2.length → Bool := fun i => c (Fin.cast he.symm i)
  have hc : Literal.extend c=Literal.extend old := Literal.extend_cast he c
  have hec : e c=Occurrence.bits g old := rfl
  rw [hec]
  simp only [Compiler.virtual,List.map_map,hc,Function.comp_def]
  have hm : ((Compiler.nodes g).map (fun p =>
      if (Compiler.ports g p.1 p.2).length=0 then (1 : ℚ)
      else if ((Compiler.ports g p.1 p.2).map (fun q => Literal.extend old q.1)).count true=1 then 1 else 0)) =
      (Compiler.nodes g).map (fun p => if (Occurrence.portWord g p.1 p.2 old).count true=1 then (1 : ℚ) else 0) := by
    apply List.map_congr_left
    intro p hp
    simp [Occurrence.nonzero_degree g hz p hp,Occurrence.portWord]
  rw [hm,Occurrence.list_product_indicator]
  by_cases h : Incidence.Selected g (Occurrence.bits g old)
  · have hl := (Occurrence.support_iff g old).mpr h
    simp only [if_pos hl,if_pos h]
  · have hl : ¬∀p∈Compiler.nodes g,(Occurrence.portWord g p.1 p.2 old).count true=1 :=
      fun hh=>h ((Occurrence.support_iff g old).mp hh)
    simp only [if_neg hl,if_neg h]

end Closed

/-- Exact physical fixed-alphabet value for the SAME compiled raw query.
The zero-degree branch is handled separately by its actual no-query code. -/
theorem query_value (g : UnitInput) (hz : Compiler.zeroTest g=false) :
    targetValue (Compiler.query g)=unitValue g := by
  rw [query_to_virtual,Closed.virtual_count g hz]

def emptyQuery : TargetInput := ⟨⟨[],[]⟩,by
  simp [RawClosedNetwork.WellFormed,RawClosedNetwork.endpoints,
    RawClosedNetwork.expectedEndpoints]⟩
theorem empty_value : targetValue emptyQuery=1 := by
  simp [targetValue,emptyQuery,RawClosedNetwork.realize,RawClosedNetwork.shape,
    Network.denote]

def zeroProgramme : Computes unitEncoding rationalEncoding (fun _ : UnitInput => (0 : ℚ)) :=
  constantComputes unitEncoding rationalEncoding 0
def oneProgramme : Computes unitEncoding rationalEncoding (fun _ : UnitInput => (1 : ℚ)) :=
  constantComputes unitEncoding rationalEncoding 1
theorem zero_value (g : UnitInput) (h : Compiler.zeroTest g=true) : unitValue g=0 := by
  simp [unitValue,Compiler.zeroTest_count g h]
theorem one_value (g : UnitInput) (h : g.val.1=0) : unitValue g=1 := by
  simp [unitValue,empty_count g h]

/-- Runtime branch specification with a proved mathematical value. The
unfinished variable-tree bit emitter is not turned into a caller input. -/
inductive Case (g : UnitInput) where
  | empty (hn : g.val.1=0)
  | zero (hz : Compiler.zeroTest g=true)
  | query (hn : 0<g.val.1) (hz : Compiler.zeroTest g=false)

/-- UnitInput is the ONLY input. It contains the original ordered full
UnitEdge list and its actual UnitValid proof. No extra ID-pair uniqueness,
matching, query, compiler certificate or desired answer is accepted. -/
def top (g : UnitInput) : Case g :=
  if hn : g.val.1=0 then .empty hn
  else if hz : Compiler.zeroTest g=true then .zero hz
  else .query (Nat.pos_of_ne_zero hn) (by cases h : Compiler.zeroTest g <;> simp_all)

def Case.queries {g : UnitInput} : Case g → List TargetInput
  | .empty _ => []
  | .zero _ => []
  | .query _ _ => [Compiler.query g]
def Case.answer {g : UnitInput} : Case g → Option ℚ
  | .empty _ => some 1
  | .zero _ => some 0
  | .query _ _ => none
def Case.value {g : UnitInput} : Case g → ℚ
  | .empty _ => 1
  | .zero _ => 0
  | .query _ _ => targetValue (Compiler.query g)

/-- Actual mathematical query-plan correctness for ALL legal UnitInputs,
including the real no-query constants. The target answer is its fixed
Holant value, never a caller-supplied correct-answer hypothesis. -/
theorem case_value {g : UnitInput} (C : Case g) : C.value=unitValue g := by
  cases C with
  | empty hn => exact (one_value g hn).symm
  | zero hz => exact (zero_value g hz).symm
  | query hn hz => exact query_value g hz
theorem top_value (g : UnitInput) : (top g).value=unitValue g := case_value (top g)

/-- Concrete consumed frontend: SAME ordered whole degree graph plus the
true zero classifier. The missing target-backend is not an input here. -/
def frontEncoding := pairEncoding RawClosedNetwork.encoding encodingBoolBool
def frontProgramme : Computes unitEncoding frontEncoding
    (fun g : UnitInput => (Compiler.virtual g,Compiler.zeroTest g)) :=
  pairComputes Programs.virtualComputes Programs.zero
theorem front_execution (g : UnitInput) : Programs.RunsExactly frontProgramme.machine.computer.step
    (initList frontProgramme.machine.computer (unitEncoding.encode g))
    (haltList frontProgramme.machine.computer
      (frontEncoding.encode (Compiler.virtual g,Compiler.zeroTest g)))
      (frontProgramme.outputs g).steps := (frontProgramme.outputs g).evals_in_steps
theorem front_time (g : UnitInput) :
    (frontProgramme.outputs g).steps≤frontProgramme.time.eval (unitEncoding.encode g).length :=
  (frontProgramme.outputs g).steps_le_m
theorem front_primitive (g : UnitInput) : primitiveCost frontProgramme.machine (frontProgramme.outputs g).steps
    (some (initList frontProgramme.machine.computer (unitEncoding.encode g)))≤
      (primitivePolynomial frontProgramme).eval (unitEncoding.encode g).length :=
  computes_primitive_cost frontProgramme g
theorem front_storage (g : UnitInput) (t : ℕ) (c : frontProgramme.machine.Config)
    (ht : t≤frontProgramme.time.eval (unitEncoding.encode g).length)
    (hr : Programs.RunsExactly frontProgramme.machine.computer.step
      (initList frontProgramme.machine.computer (unitEncoding.encode g)) c t) :
    stackSize c.stk≤frontProgramme.outputBound.bound.eval (unitEncoding.encode g).length := by
  have h := frontProgramme.machine.run_size_le _ _ _ hr
  rw [Machine.size_init] at h
  exact h.trans (by
    simpa only [Computes.outputBound,Polynomial.eval_add,Polynomial.eval_X,
      Polynomial.eval_mul,Polynomial.eval_C] using
      Nat.add_le_add_left (Nat.mul_le_mul_right frontProgramme.machine.primitiveBudget ht)
        (unitEncoding.encode g).length)

theorem terminal_answer {g : UnitInput} (C : Case g) (a : ℚ)
    (ha : C.answer=some a) : a=unitValue g := by
  cases C with
  | empty hn =>
      have he : a=1 := (Option.some.inj ha).symm
      rw [he,one_value g hn]
  | zero hz =>
      have he : a=0 := (Option.some.inj ha).symm
      rw [he,zero_value g hz]
  | query hn hz => cases ha

theorem queries_bound {g : UnitInput} (C : Case g) : C.queries.length≤1 := by
  cases C <;> simp [Case.queries]
theorem query_bytes {g : UnitInput} (C : Case g) (q : TargetInput) (hq : q∈C.queries) :
    targetEncoding.decode (targetEncoding.encode q)=some q ∧
    (targetEncoding.encode q).length≤Compiler.bitBudget (unitEncoding.encode g).length := by
  cases C with
  | empty _ => simp [Case.queries] at hq
  | zero _ => simp [Case.queries] at hq
  | query _ _ =>
      have he : q=Compiler.query g := List.mem_singleton.mp hq
      subst q
      exact ⟨targetEncoding.decode_encode _,Compiler.query_bits_bound g⟩

/-- The original structural receipt is preserved. query_value/top_value
now supply the stronger physical value equality; the dynamic target-bit
backend still prevents claiming a full finite-machine oracle reduction. -/
theorem top_receipt (g : UnitInput) :
    Incidence.partition g=unitValue g ∧
    (Compiler.queryRaw g).WellFormed 3 1 Tree.arity ∧
    (Compiler.queryBits g).length≤Compiler.bitBudget (unitEncoding.encode g).length ∧
    (top g).queries.length≤1 := by
  exact ⟨Incidence.partition_count g,Compiler.query_valid g,
    Compiler.query_bits_bound g,queries_bound (top g)⟩

/-- Fixed terminal programs have true finite Boolean syntax and primitive
budgets. These bounds concern CONSTANT answers only; the unfinished graph
compiler is not granted a caller-provided clock by this statement. -/
theorem zero_primitive_budget (label : Bool) :
    TM2Cost.budget ((Constant.machine (rationalEncoding.encode (0 : ℚ))).program label)≤
      (rationalEncoding.encode (0 : ℚ)).length+4 := Constant.program_budget _ _
theorem one_primitive_budget (label : Bool) :
    TM2Cost.budget ((Constant.machine (rationalEncoding.encode (1 : ℚ))).program label)≤
      (rationalEncoding.encode (1 : ℚ)).length+4 := Constant.program_budget _ _

end Holant.LocalDrafts.CountingHardness.UnitPerfectMatchingHolant.Source
