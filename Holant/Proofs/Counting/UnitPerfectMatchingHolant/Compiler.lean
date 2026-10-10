import Holant.Proofs.Counting.UnitPerfectMatchingHolant.Incidence
import Holant.Complexity.FixedGadgetSubstitution.Size


namespace Holant.LocalDrafts.CountingHardness.UnitPerfectMatchingHolant.Compiler
open Holant Holant.Complexity FixedGadgetSubstitution
open Holant.LocalDrafts.Hardness.EightVertexNonexception.SixVertexInterpolation.VerifierGates.WeightedMatchingInterpolation

def occurrence (g : UnitInput) (i : Fin g.val.2.length) : UnitEdges g :=
  ⟨g.val.2.get i,List.mem_toFinset.mpr (List.get_mem _ i)⟩
theorem occurrence_injective (g : UnitInput) : Function.Injective (occurrence g) := by
  intro i j h
  exact g.property.1.injective_get (congrArg Subtype.val h)
theorem occurrence_surjective (g : UnitInput) : Function.Surjective (occurrence g) := by
  intro e
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp (List.mem_toFinset.mp e.property)
  exact ⟨i,Subtype.ext hi⟩
/-- This identifies LIST POSITIONS with COMPLETE records, using precisely
the input's Nodup proof; repeated ID pairs or endpoints are not collapsed. -/
noncomputable def occurrenceEquiv (g : UnitInput) : Fin g.val.2.length ≃ UnitEdges g :=
  Equiv.ofBijective (occurrence g) ⟨occurrence_injective g,occurrence_surjective g⟩

/-- false=row and true=column, in two disjoint consecutive vertex blocks. -/
def nodes (g : UnitInput) : List (Bool × ℕ) :=
  (List.range g.val.1).map (false,·) ++ (List.range g.val.1).map (true,·)
def endpoint (g : UnitInput) (side : Bool) (i : ℕ) : ℕ :=
  let e := g.val.2.getD i ((0,0),(0,0))
  if side then e.2.2 else e.2.1
theorem endpoint_occurrence (g : UnitInput) (side : Bool) (i : Fin g.val.2.length) :
    endpoint g side i.val=
      (if side then (occurrence g i).val.2.2 else (occurrence g i).val.2.1) := by
  simp [endpoint,occurrence,List.getD_eq_getElem _ _ i.isLt,List.get_eq_getElem]
/-- Port order is original occurrence-list order. The edge ID in the raw
network is its LIST POSITION, not its possibly repeated ID-pair field. -/
def ports (g : UnitInput) (side : Bool) (r : ℕ) : List RawEndpoint :=
  (List.range g.val.2.length).flatMap fun i =>
    if endpoint g side i=r then [(i,side)] else []
def virtual (g : UnitInput) : RawClosedNetwork :=
  ⟨(nodes g).map (fun p => ((ports g p.1 p.2).length,ports g p.1 p.2)),
    List.replicate g.val.2.length 0⟩

def degreeTemplate : ℕ → Template
  | 0 => ⟨0,[],[]⟩ -- ONLY a validator placeholder; degree zero is intercepted.
  | 1 => ⟨1,[(2,[.inl 0])],[]⟩
  | 2 => ⟨2,[(1,[.inl 0,.inl 1])],[]⟩
  | m+3 => Tree.template m
def queryRaw (g : UnitInput) : RawClosedNetwork := replace degreeTemplate (virtual g)
def zeroTest (g : UnitInput) : Bool :=
  (nodes g).any (fun p => (ports g p.1 p.2).isEmpty)

theorem degree_boundary (d : ℕ) : (degreeTemplate d).boundary=d := by
  rcases d with _ | _ | _ | m
  · rfl
  · rfl
  · rfl
  · exact (Tree.template_counts m).1
theorem degree_valid (d : ℕ) : (degreeTemplate d).WellFormed 3 1 Tree.arity := by
  rcases d with _ | _ | _ | m
  · simp [degreeTemplate,Template.WellFormed,Template.endpoints,
      Template.expectedEndpoints,edgeEnds]
  · simp [degreeTemplate,Template.WellFormed,Template.endpoints,
      Template.expectedEndpoints,edgeEnds,Tree.arity,List.range_succ]
  · simp [degreeTemplate,Template.WellFormed,Template.endpoints,
      Template.expectedEndpoints,edgeEnds,Tree.arity,List.range_succ]
  · exact Tree.template_wellFormed m
theorem degree_counts (d : ℕ) :
    (degreeTemplate d).vertices.length≤2*d ∧ (degreeTemplate d).edges.length≤2*d := by
  rcases d with _ | _ | _ | m
  · simp [degreeTemplate]
  · simp [degreeTemplate]
  · simp [degreeTemplate]
  · have h := Tree.template_counts m
    change (Tree.template m).vertices.length≤2*(m+3) ∧
      (Tree.template m).edges.length≤2*(m+3)
    rw [h.2.1,h.2.2]
    omega

private theorem flatMap_exchange {α β γ : Type} (xs : List α) (ys : List β)
    (f : α → β → List γ) :
    (xs.flatMap (fun x => ys.flatMap (f x))).Perm
      (ys.flatMap (fun y => xs.flatMap (fun x => f x y))) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.flatMap_cons]
      exact ((List.Perm.refl _).append ih).trans
        (List.flatMap_append_perm ys (f x) (fun y => xs.flatMap (fun x => f x y)))

private theorem scan_miss {α : Type} (a : α) (k n : ℕ) (hk : n≤k) :
    (List.range n).flatMap (fun r => if k=r then [a] else [])=[] := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.range_succ,List.flatMap_append]
      rw [ih (by omega)]
      simp [show k≠n by omega]
private theorem scan_hit {α : Type} (a : α) (k n : ℕ) (hk : k<n) :
    (List.range n).flatMap (fun r => if k=r then [a] else [])=[a] := by
  induction n with
  | zero => omega
  | succ n ih =>
      rw [List.range_succ,List.flatMap_append]
      by_cases h : k=n
      · subst k
        rw [scan_miss a n n (by omega)]
        simp
      · rw [ih (by omega)]
        simp [h]

theorem endpoint_bound (g : UnitInput) (side : Bool) (i : ℕ)
    (hi : i<g.val.2.length) : endpoint g side i<g.val.1 := by
  have h := g.property.2 (g.val.2.getD i ((0,0),(0,0))) (by
    rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem hi)
  cases side with
  | false => exact h.1
  | true => exact h.2

theorem ports_bound (g : UnitInput) (side : Bool) (r : ℕ) :
    (ports g side r).length≤g.val.2.length := by
  unfold ports
  have h : ∀ xs : List ℕ,
      (xs.flatMap (fun i => if endpoint g side i=r then [(i,side)] else [])).length≤xs.length := by
    intro xs
    induction xs with
    | nil => simp
    | cons i xs ih =>
        by_cases he : endpoint g side i=r <;>
          simp only [List.flatMap_cons,he,if_true,if_false,List.nil_append,
            List.cons_append,List.length_cons,List.length_nil] <;> omega
  simpa using h (List.range g.val.2.length)

theorem virtual_endpoints (g : UnitInput) :
    (virtual g).endpoints.Perm (virtual g).expectedEndpoints := by
  rw [expectedEndpoints_eq]
  simp only [virtual, RawClosedNetwork.endpoints, List.map_map, Function.comp_def]
  change ((nodes g).flatMap (fun p =>
      (List.range g.val.2.length).flatMap (fun i =>
        if endpoint g p.1 i=p.2 then [(i,p.1)] else []))).Perm _
  apply (flatMap_exchange (nodes g) (List.range g.val.2.length)
    (fun p i => if endpoint g p.1 i=p.2 then [(i,p.1)] else [])).trans
  have hf : ∀ i ∈ List.range g.val.2.length,
      (nodes g).flatMap (fun p => if endpoint g p.1 i=p.2 then [(i,p.1)] else []) =
        [(i,false),(i,true)] := by
    intro i hi
    have h0 := endpoint_bound g false i (List.mem_range.mp hi)
    have h1 := endpoint_bound g true i (List.mem_range.mp hi)
    simp only [nodes,List.flatMap_append,List.flatMap_map,Function.comp_def]
    rw [scan_hit (i,false) (endpoint g false i) g.val.1 h0,
      scan_hit (i,true) (endpoint g true i) g.val.1 h1]
    rfl
  have hp : ((List.range g.val.2.length).flatMap (fun i =>
      (nodes g).flatMap (fun p => if endpoint g p.1 i=p.2 then [(i,p.1)] else []))).Perm
      ((List.range g.val.2.length).flatMap (fun i => [(i,false),(i,true)])) :=
    List.Perm.flatMap_left _ (fun i hi => by
      simpa only [hf i hi] using List.Perm.refl [(i,false),(i,true)])
  simpa [virtual,edgeEnds] using hp

theorem virtual_valid (g : UnitInput) :
    (virtual g).WellFormed (g.val.2.length+1) 1 id := by
  refine ⟨?_,?_,virtual_endpoints g⟩
  · intro v
    have hm := List.get_mem (virtual g).vertices v
    obtain ⟨p,hp,he⟩ := List.mem_map.mp hm
    rw [←he]
    exact ⟨by have h := ports_bound g p.1 p.2; dsimp; omega,rfl⟩
  · intro e
    have h := List.get_mem (virtual g).edges e
    have he : (virtual g).edges.get e=0 := List.mem_replicate.mp h |>.2
    rw [he]
    decide

/-- The whole compiler output passes the SAME existing faithful validator.
No layout, query equality or well-formedness certificate is caller supplied. -/
theorem query_valid (g : UnitInput) : (queryRaw g).WellFormed 3 1 Tree.arity :=
  replace_wellFormed degreeTemplate (virtual g) (virtual_valid g)
    (fun d _ => ⟨degree_valid d,degree_boundary d⟩)
def query (g : UnitInput) : {r : RawClosedNetwork // r.WellFormed 3 1 Tree.arity} :=
  ⟨queryRaw g,query_valid g⟩
def queryBits (g : UnitInput) : List Bool :=
  (RawClosedNetwork.validatedEncoding 3 1 Tree.arity).encode (query g)
theorem query_decode (g : UnitInput) :
    (RawClosedNetwork.validatedEncoding 3 1 Tree.arity).decode (queryBits g)=some (query g) :=
  (RawClosedNetwork.validatedEncoding 3 1 Tree.arity).decode_encode _

/-- The original edge block is unchanged, including orientation and every
parallel occurrence. Internal Eq labels are appended after that block. -/
theorem query_edge_block (g : UnitInput) :
    (queryRaw g).edges=List.replicate g.val.2.length 0 ++
      (expandRows degreeTemplate g.val.2.length (virtual g).vertices).edges := by
  simp [queryRaw,replace,virtual]
theorem query_counts (g : UnitInput) :
    (queryRaw g).vertices.length≤4*g.val.1*g.val.2.length ∧
    (queryRaw g).edges.length≤g.val.2.length+4*g.val.1*g.val.2.length := by
  have hn : (virtual g).vertices.length=2*g.val.1 := by simp [virtual,nodes]; omega
  have hrow : ∀ row ∈ (virtual g).vertices,
      (degreeTemplate row.1).vertices.length≤2*g.val.2.length ∧
      (degreeTemplate row.1).edges.length≤2*g.val.2.length := by
    intro row hr
    obtain ⟨p,_,rfl⟩ := List.mem_map.mp hr
    have hd := degree_counts (ports g p.1 p.2).length
    have hb := ports_bound g p.1 p.2
    exact ⟨hd.1.trans (Nat.mul_le_mul_left 2 hb),
      hd.2.trans (Nat.mul_le_mul_left 2 hb)⟩
  have hv := sum_map_le (fun row : RawVertex => (degreeTemplate row.1).vertices.length)
    (virtual g).vertices (2*g.val.2.length) (fun row hr => (hrow row hr).1)
  have he := sum_map_le (fun row : RawVertex => (degreeTemplate row.1).edges.length)
    (virtual g).vertices (2*g.val.2.length) (fun row hr => (hrow row hr).2)
  rw [hn] at hv he
  unfold queryRaw
  rw [replace_vertex_count,replace_edge_count]
  have hg : (virtual g).edges.length=g.val.2.length := by simp [virtual]
  rw [hg]
  constructor <;> nlinarith

def bitBudget (N : ℕ) : ℕ :=
  (108+48*(N+4*N^2))*(4*N^2)+4*(N+4*N^2)+4
theorem query_bits_bound (g : UnitInput) :
    (queryBits g).length≤bitBudget (unitEncoding.encode g).length := by
  let N := (unitEncoding.encode g).length
  have hi := unit_input_counts g
  have hc := query_counts g
  have hnm : g.val.1*g.val.2.length≤N^2 := by
    simpa [N,pow_two] using Nat.mul_le_mul hi.1 hi.2
  have hv : (queryRaw g).vertices.length≤4*N^2 := by nlinarith [hc.1]
  have he : (queryRaw g).edges.length≤N+4*N^2 := by dsimp [N] at *; nlinarith [hc.2]
  have ha : ∀ d<3,Tree.arity d≤3 := by
    intro d hd
    interval_cases d <;> decide
  have h := raw_length_le (queryRaw g) (query_valid g) 3 ha
  have hp := Nat.mul_le_mul he hv
  change (RawClosedNetwork.encoding.encode (queryRaw g)).length≤bitBudget N
  unfold bitBudget
  nlinarith

theorem ports_contains (g : UnitInput) (e : UnitEdges g) (side : Bool) :
    ∃ i,(i,side)∈ports g side (if side then e.val.2.2 else e.val.2.1) := by
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp (List.mem_toFinset.mp e.property)
  have he : endpoint g side i.val=(if side then e.val.2.2 else e.val.2.1) := by
    unfold endpoint
    rw [List.getD_eq_getElem _ _ i.isLt,←List.get_eq_getElem,hi]
  refine ⟨i.val,?_⟩
  simp only [ports,List.mem_flatMap,List.mem_range]
  refine ⟨i.val,i.isLt,?_⟩
  simp [he]

theorem zeroTest_count (g : UnitInput) (h : zeroTest g=true) : unitCount g=0 := by
  change (nodes g).any (fun p => (ports g p.1 p.2).isEmpty)=true at h
  obtain ⟨p,hp,hz⟩ := List.any_eq_true.mp h
  have hnil : ports g p.1 p.2=[] := by
    cases he : ports g p.1 p.2 with
    | nil => rfl
    | cons x xs => simp [he] at hz
  have hn : p.2<g.val.1 := by
    change p∈(List.range g.val.1).map (false,·) ++ (List.range g.val.1).map (true,·) at hp
    rcases List.mem_append.mp hp with h0 | h1
    · obtain ⟨r,hr,he⟩ := List.mem_map.mp h0
      rw [←he]
      exact List.mem_range.mp hr
    · obtain ⟨r,hr,he⟩ := List.mem_map.mp h1
      rw [←he]
      exact List.mem_range.mp hr
  cases hb : p.1 with
  | false =>
      apply Incidence.isolated_row_zero g ⟨p.2,hn⟩
      intro e he
      obtain ⟨i,hi⟩ := ports_contains g e false
      have hnil' : ports g false p.2=[] := by simpa only [hb] using hnil
      simpa [he,hnil'] using hi
  | true =>
      apply Incidence.isolated_column_zero g ⟨p.2,hn⟩
      intro e he
      obtain ⟨i,hi⟩ := ports_contains g e true
      have hnil' : ports g true p.2=[] := by simpa only [hb] using hnil
      simpa [he,hnil'] using hi

theorem empty_raw (g : UnitInput) (h : g.val.1=0) : queryRaw g=⟨[],[]⟩ := by
  have hes : g.val.2=[] := by
    cases he : g.val.2 with
    | nil => rfl
    | cons e es =>
        have ht := (g.property.2 e (by simp [he])).1
        omega
  simp [queryRaw,replace,virtual,nodes,h,hes,expandRows]

end Holant.LocalDrafts.CountingHardness.UnitPerfectMatchingHolant.Compiler
