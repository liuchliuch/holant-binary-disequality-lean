import Holant.Proofs.Reductions.EightVertexNonexception.SixVertexInterpolation.VerifierGates.NativeCubicMatching.Incidence
import Holant.Complexity.FixedGadgetSubstitution.Size


noncomputable section
namespace Holant.LocalDrafts.Hardness.EightVertexNonexception.SixVertexInterpolation.VerifierGates.NativeCubicMatching
open Holant Holant.Complexity FixedGadgetSubstitution
open WeightedMatchingInterpolation
namespace Layout

def tag (side : Bool) : ℕ := if side then 1 else 0
theorem tag_bound (side : Bool) : tag side<2 := by cases side <;> decide
def moved (m : ℕ) : LocalEndpoint → LocalEndpoint
  | .inl 0 => .inr (m,false)
  | .inl (k+1) => .inl (k+2)
  | .inr p => .inr p
def tree (side : Bool) : ℕ → Template
  | 0 => ⟨3,[(tag side,[.inl 0,.inl 1,.inl 2])],[]⟩
  | m+1 =>
      let old := tree side m
      ⟨m+4,old.vertices.map (fun row => (row.1,row.2.map (moved m))) ++
        [(tag side,[.inl 0,.inl 1,.inr (m,true)])],old.edges++[0]⟩
theorem tree_counts (side : Bool) (m : ℕ) :
    (tree side m).boundary=m+3 ∧ (tree side m).vertices.length=m+1 ∧
      (tree side m).edges.length=m := by
  induction m with
  | zero => simp [tree]
  | succ m ih => simp [tree,ih.2.1,ih.2.2] <;> omega
theorem tree_labels (side : Bool) (m : ℕ) :
    ∀ row∈(tree side m).vertices,row.1<2 ∧ row.2.length=arity row.1 := by
  induction m with
  | zero => cases side <;> simp [tree,arity,tag]
  | succ m ih =>
      intro row hr
      simp only [tree,List.mem_append,List.mem_map,List.mem_singleton] at hr
      rcases hr with ⟨r,hr,rfl⟩ | rfl
      · simpa [arity] using ih r hr
      · exact ⟨tag_bound side,rfl⟩

private theorem boundary_tail (m : ℕ) :
    ((List.range (m+3)).map Sum.inl).map (moved m)=
      .inr (m,false)::(List.range (m+2)).map (fun i => Sum.inl (i+2)) := by
  have h : m+3=(m+2)+1 := by omega
  rw [h,List.range_succ_eq_map]
  simp [List.map_map,Function.comp_def,moved]
private theorem boundary_head (n : ℕ) :
    (List.range (n+2)).map (Sum.inl : ℕ → LocalEndpoint)=
      [.inl 0,.inl 1]++(List.range n).map (fun i => .inl (i+2)) := by
  simp [List.range_succ_eq_map,List.map_map,Function.comp_def,Nat.add_assoc]
private theorem endpoints_step (side : Bool) (m : ℕ) :
    (tree side (m+1)).endpoints=(tree side m).endpoints.map (moved m)++
      [.inl 0,.inl 1,.inr (m,true)] := by
  simp [tree,Template.endpoints,List.map_flatten,List.map_map,Function.comp_def]

theorem tree_endpoints (side : Bool) (m : ℕ) :
    (tree side m).endpoints.Perm (tree side m).expectedEndpoints := by
  induction m with
  | zero => simp [tree,Template.endpoints,Template.expectedEndpoints,edgeEnds,List.range_succ]
  | succ m ih =>
      let bs : List LocalEndpoint := (List.range (m+2)).map (fun i => .inl (i+2))
      let es : List LocalEndpoint := (edgeEnds 0 m).map Sum.inr
      have old : (tree side m).expectedEndpoints.map (moved m)=
          .inr (m,false)::(bs++es) := by
        rw [Template.expectedEndpoints,(tree_counts side m).1,(tree_counts side m).2.2]
        simp only [List.map_append]
        rw [boundary_tail]
        simp [bs,es,List.map_map,Function.comp_def,moved]
      have target : (tree side (m+1)).expectedEndpoints=
          [.inl 0,.inl 1]++bs++es++[.inr (m,false),.inr (m,true)] := by
        rw [Template.expectedEndpoints,(tree_counts side (m+1)).1,
          (tree_counts side (m+1)).2.2]
        have h : m+1+3=(m+2)+2 := by omega
        rw [h,boundary_head,edgeEnds_add]
        simp [bs,es,edgeEnds,List.map_append,List.append_assoc]
      rw [endpoints_step,target]
      have h := (ih.map (moved m)).append_right [.inl 0,.inl 1,.inr (m,true)]
      rw [old] at h
      apply h.trans
      classical
      letI : BEq LocalEndpoint := ⟨fun a b => decide (a=b)⟩
      letI : LawfulBEq LocalEndpoint := {
        eq_of_beq := by
          intro a b h
          change decide (a=b)=true at h
          exact of_decide_eq_true h
        rfl := by
          intro a
          change decide (a=a)=true
          simp }
      apply List.perm_iff_count.mpr
      intro p
      simp only [List.count_append,List.count_cons,List.count_nil]
      omega
theorem tree_valid (side : Bool) (m : ℕ) : (tree side m).WellFormed 2 1 arity := by
  refine ⟨tree_labels side m,?_,tree_endpoints side m⟩
  intro e he
  have h : ∀ k,∀ e∈(tree side k).edges,e<1 := by
    intro k
    induction k with
    | zero => simp [tree]
    | succ k ih =>
        intro e he
        simp only [tree,List.mem_append,List.mem_singleton] at he
        rcases he with he | rfl
        · exact ih e he
        · decide
  exact h m e he

def lowMain (side : Bool) (d : ℕ) : LocalVertex :=
  (tag side,(List.range d).map Sum.inl++
    (List.range (3-d)).map (fun k => .inr (2*k,false)))
def lowPad (side : Bool) (k : ℕ) : LocalVertex :=
  (tag (!side),[.inr (2*k+1,false),.inr (2*k+1,true),.inr (2*k,true)])
def low (side : Bool) (d : ℕ) : Template :=
  ⟨d,[lowMain side d]++(List.range (3-d)).map (lowPad side),
    List.replicate (2*(3-d)) 0⟩
theorem low_valid (side : Bool) (d : ℕ) (hd : d≤3) : (low side d).WellFormed 2 1 arity := by
  interval_cases d <;> cases side <;>
    simp [low,lowMain,lowPad,tag,arity,Template.WellFormed,Template.endpoints,
      Template.expectedEndpoints,edgeEnds]
  all_goals decide +kernel
theorem low_counts (side : Bool) (d : ℕ) :
    (low side d).boundary=d ∧ (low side d).vertices.length=1+(3-d) ∧
      (low side d).edges.length=2*(3-d) := by simp [low,Nat.add_comm]

def degree (side : Bool) (d : ℕ) : Template :=
  if d≤3 then low side d else tree side (d-3)
theorem degree_boundary (side : Bool) (d : ℕ) : (degree side d).boundary=d := by
  unfold degree
  split_ifs with h
  · rfl
  · rw [(tree_counts side _).1]
    omega
theorem degree_valid (side : Bool) (d : ℕ) : (degree side d).WellFormed 2 1 arity := by
  unfold degree
  split_ifs with h
  · exact low_valid side d h
  · exact tree_valid side _
theorem degree_counts (side : Bool) (d : ℕ) :
    (degree side d).vertices.length=(d-3)+1+(3-d) ∧
      (degree side d).edges.length=(d-3)+2*(3-d) := by
  unfold degree
  split_ifs with h
  · rw [(low_counts side d).2.1,(low_counts side d).2.2]
    simp [show d-3=0 by omega]
  · rw [(tree_counts side _).2.1,(tree_counts side _).2.2]
    simp [show 3-d=0 by omega]

def templates (k : ℕ) : Template := degree (k%2==1) (k/2)
theorem templates_boundary (k : ℕ) : (templates k).boundary=k/2 := degree_boundary _ _
theorem templates_valid (k : ℕ) : (templates k).WellFormed 2 1 arity := degree_valid _ _
def virtual (g : UnitInput) : RawClosedNetwork :=
  ⟨(OldCompiler.nodes g).map (fun p =>
    (2*(OldCompiler.ports g p.1 p.2).length+tag p.1,OldCompiler.ports g p.1 p.2)),
      List.replicate g.val.2.length 0⟩
def raw (g : UnitInput) : RawClosedNetwork := replace templates (virtual g)
theorem original_edges (g : UnitInput) :
    (raw g).edges=List.replicate g.val.2.length 0++
      (expandRows templates g.val.2.length (virtual g).vertices).edges := by
  simp [raw,replace,virtual]

theorem virtual_valid (g : UnitInput) :
    (virtual g).WellFormed (2*(g.val.2.length+1)) 1 (sourceArity templates) := by
  refine ⟨?_,?_,?_⟩
  · intro v
    have hm := List.get_mem (virtual g).vertices v
    obtain ⟨p,_hp,he⟩ := List.mem_map.mp hm
    rw [←he]
    have hd := OldCompiler.ports_bound g p.1 p.2
    have ht := tag_bound p.1
    refine ⟨by dsimp; omega,?_⟩
    change (OldCompiler.ports g p.1 p.2).length=
      (templates (2*(OldCompiler.ports g p.1 p.2).length+tag p.1)).boundary
    rw [templates_boundary]
    omega
  · intro e
    have h := List.get_mem (virtual g).edges e
    have he : (virtual g).edges.get e=0 := (List.mem_replicate.mp h).2
    rw [he]
    decide
  · have he : (virtual g).endpoints=(OldCompiler.virtual g).endpoints := by
      simp [virtual,OldCompiler.virtual,RawClosedNetwork.endpoints,List.map_map,Function.comp_def]
    rw [he]
    exact OldCompiler.virtual_endpoints g

theorem valid (g : UnitInput) : (raw g).WellFormed 2 1 arity :=
  query_wellFormed templates (virtual g) (virtual_valid g) (fun k _ => templates_valid k)
def query (g : UnitInput) : {r : RawClosedNetwork // r.WellFormed 2 1 arity} := ⟨raw g,valid g⟩
def queryBits (g : UnitInput) : List Bool :=
  (RawClosedNetwork.validatedEncoding 2 1 arity).encode (query g)
theorem decode_query (g : UnitInput) :
    (RawClosedNetwork.validatedEncoding 2 1 arity).decode (queryBits g)=some (query g) :=
  (RawClosedNetwork.validatedEncoding 2 1 arity).decode_encode _

theorem native_port_arity (g : UnitInput) (v : Fin (raw g).vertices.length) :
    ((raw g).vertices.get v).2.length=3 := (valid g).1 v |>.2
theorem native_label (g : UnitInput) (v : Fin (raw g).vertices.length) :
    ((raw g).vertices.get v).1<2 := (valid g).1 v |>.1

theorem counts (g : UnitInput) :
    (raw g).vertices.length≤2*g.val.1*(g.val.2.length+4) ∧
      (raw g).edges.length≤g.val.2.length+2*g.val.1*(g.val.2.length+6) := by
  have hn : (virtual g).vertices.length=2*g.val.1 := by simp [virtual,OldCompiler.nodes]; omega
  have hrow : ∀ row∈(virtual g).vertices,
      (templates row.1).vertices.length≤g.val.2.length+4 ∧
      (templates row.1).edges.length≤g.val.2.length+6 := by
    intro row hr
    obtain ⟨p,_hp,rfl⟩ := List.mem_map.mp hr
    have hd := OldCompiler.ports_bound g p.1 p.2
    have ht := tag_bound p.1
    have hq : (2*(OldCompiler.ports g p.1 p.2).length+tag p.1)/2=
        (OldCompiler.ports g p.1 p.2).length := by omega
    dsimp only [templates]
    rw [hq]
    rw [(degree_counts _ _).1,(degree_counts _ _).2]
    constructor <;> omega
  have hv := sum_map_le (fun row : RawVertex => (templates row.1).vertices.length)
    (virtual g).vertices (g.val.2.length+4) (fun row hr => (hrow row hr).1)
  have he := sum_map_le (fun row : RawVertex => (templates row.1).edges.length)
    (virtual g).vertices (g.val.2.length+6) (fun row hr => (hrow row hr).2)
  rw [hn] at hv he
  unfold raw
  rw [replace_vertex_count,replace_edge_count]
  have hg : (virtual g).edges.length=g.val.2.length := by simp [virtual]
  rw [hg]
  exact ⟨by simpa only [mul_comm] using hv,
    by simpa only [mul_comm] using Nat.add_le_add_left he g.val.2.length⟩

def bitBudget (N : ℕ) : ℕ :=
  (108+48*(N+2*N*(N+6)))*(2*N*(N+4))+4*(N+2*N*(N+6))+4
theorem bit_bound (g : UnitInput) : (queryBits g).length≤bitBudget (unitEncoding.encode g).length := by
  let N := (unitEncoding.encode g).length
  have hi := unit_input_counts g
  have hc := counts g
  have hv : (raw g).vertices.length≤2*N*(N+4) := by
    dsimp [N]
    nlinarith [Nat.mul_le_mul hi.1 (Nat.add_le_add_right hi.2 4)]
  have he : (raw g).edges.length≤N+2*N*(N+6) := by
    dsimp [N]
    nlinarith [Nat.mul_le_mul hi.1 (Nat.add_le_add_right hi.2 6)]
  have h := raw_length_le (raw g) (valid g) 3 (fun _ _ => le_refl 3)
  have hp := Nat.mul_le_mul he hv
  change (RawClosedNetwork.encoding.encode (raw g)).length≤bitBudget N
  unfold bitBudget
  nlinarith

end Layout
end Holant.LocalDrafts.Hardness.EightVertexNonexception.SixVertexInterpolation.VerifierGates.NativeCubicMatching
