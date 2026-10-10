import Holant.Proofs.Reductions.EightVertexNonexception.SixVertexInterpolation.VerifierGates.NativeCubicMatching.Layout
import Holant.Complexity.FixedGadgetSubstitution.Partition
import Holant.ChargeConservation


noncomputable section
namespace Holant.LocalDrafts.Hardness.EightVertexNonexception.SixVertexInterpolation.VerifierGates.NativeCubicMatching
open Holant Holant.Complexity FixedGadgetSubstitution
open scoped BigOperators
namespace Literal
set_option backward.isDefEq.respectTransparency false
local instance : Fintype OldTree.Wire := @instFintypeProd Bool Bool Bool.fintype Bool.fintype

def normal (side b : Bool) : Bool := if side then !b else b
@[simp] theorem normal_twice (side b : Bool) : normal side (normal side b)=b := by
  cases side <;> cases b <;> rfl
def extend {n : ℕ} (z : (Fin n × Bool) → Bool) (p : ℕ × Bool) : Bool :=
  if h : p.1<n then z (⟨p.1,h⟩,p.2) else false
def slot (w : List Bool) (c : (ℕ × Bool) → Bool) : LocalEndpoint → Bool
  | .inl i => w.getD i false
  | .inr p => c p
def gate (k : ℕ) (a : ℕ → Bool) : ℚ :=
  if k=0 then ONE (fun i => a i.val) else TWO (fun i => a i.val)
def rowWeight (w : List Bool) (c : (ℕ × Bool) → Bool) (r : LocalVertex) : ℚ :=
  gate r.1 (fun i => slot w c (r.2.getD i (.inl 0)))
def rowsWeight (w : List Bool) (c : (ℕ × Bool) → Bool) (rs : List LocalVertex) : ℚ :=
  (rs.map (rowWeight w c)).prod
def partition (T : Template) (w : List Bool) : ℚ :=
  ∑ z : (Fin T.edges.length × Bool) → Bool,
    rowsWeight w (extend z) T.vertices *
      ∏ e : Fin T.edges.length,Signature.disequality (z (e,false)) (z (e,true))

theorem gate_palette (i : Fin 2) (a : ℕ → Bool) :
    gate i.val a=palette i (fun j => a j.val) := by fin_cases i <;> rfl
theorem extend_at {n : ℕ} (z : (Fin n × Bool) → Bool) (e : Fin n) (b : Bool) :
    extend z (e.val,b)=z (e,b) := by simp [extend,e.isLt]
theorem slot_embed {n e : ℕ} (x : Fin n → Bool) (z : (Fin e × Bool) → Bool)
    (p : Fin n ⊕ (Fin e × Bool)) :
    slot (List.ofFn x) (extend z) (Template.embed n e p)=Sum.elim x z p := by
  cases p with
  | inl i =>
      simp only [Template.embed,Sum.elim_inl,slot]
      rw [List.getD_eq_getElem _ _ (by simpa using i.isLt)]
      simp
  | inr p => exact extend_at z p.1 p.2
theorem assigned_port (T : Template) (hT : T.WellFormed 2 1 arity)
    (x : Fin T.boundary → Bool) (z : (Fin T.edges.length × Bool) → Bool)
    (v : Fin T.vertices.length) (i : Fin 3) :
    (T.network hT palette edge).shape.assignment x z v i=
      slot (List.ofFn x) (extend z) ((T.vertices.get v).2.getD i.val (.inl 0)) := by
  change Sum.elim x z (T.route hT ⟨v,i⟩)=_
  rw [←slot_embed x z (T.route hT ⟨v,i⟩),Template.embed_route]
  unfold Template.portEndpoint
  have hi : i.val<(T.vertices.get v).2.length := by
    rw [(hT.1 _ (List.get_mem _ v)).2]
    exact i.isLt
  rw [List.getD_eq_getElem _ _ hi,List.get_eq_getElem]
  rfl
theorem template_partition (T : Template) (hT : T.WellFormed 2 1 arity)
    (x : Fin T.boundary → Bool) :
    (T.network hT palette edge).denote x=partition T (List.ofFn x) := by
  unfold Network.denote partition
  apply Finset.sum_congr rfl
  intro z _
  change (Fin T.edges.length × Bool) → Bool at z
  congr 1
  unfold rowsWeight
  rw [←List.ofFn_getElem_eq_map T.vertices (rowWeight (List.ofFn x) (extend z)),List.prod_ofFn]
  apply Finset.prod_congr rfl
  intro v _
  change Fin T.vertices.length at v
  change (T.network hT palette edge).vertex v ((T.network hT palette edge).shape.assignment x z v) =
    rowWeight (List.ofFn x) (extend z) (T.vertices.get v)
  unfold rowWeight
  rw [gate_palette ⟨(T.vertices.get v).1,(hT.1 _ (List.get_mem _ v)).1⟩]
  congr 1
  funext i
  exact assigned_port T hT x z v i

theorem slot_moved (m : ℕ) (w : List Bool) (c : (ℕ × Bool) → Bool) (p : LocalEndpoint) :
    slot w c (Layout.moved m p)=slot (c (m,false)::w.drop 2) c p := by
  cases p with
  | inl i =>
      cases i with
      | zero => rfl
      | succ i => cases w with
        | nil => rfl
        | cons a w => cases w <;> rfl
  | inr p => rfl
theorem row_moved (m : ℕ) (w : List Bool) (c : (ℕ × Bool) → Bool) (r : LocalVertex)
    (hr : r.2.length=3) :
    rowWeight w c (r.1,r.2.map (Layout.moved m))=
      rowWeight (c (m,false)::w.drop 2) c r := by
  unfold rowWeight gate
  split_ifs
  all_goals
    congr 1
    funext i
    have hi : i.val<r.2.length := by rw [hr]; exact i.isLt
    change slot w c ((r.2.map (Layout.moved m)).getD i.val (.inl 0)) =
      slot (c (m,false)::w.drop 2) c (r.2.getD i.val (.inl 0))
    rw [List.getD_eq_getElem _ _ (by simpa using hi),List.getD_eq_getElem _ _ hi]
    simp only [List.getElem_map]
    exact slot_moved m w c _

def internalWord (side : Bool) : ℕ → ((ℕ × Bool) → Bool) → List OldTree.Wire
  | 0,_ => []
  | m+1,c => (normal side (c (m,true)),normal side (c (m,false)))::internalWord side m c
theorem internalWord_congr (side : Bool) (m : ℕ) (c e : (ℕ × Bool) → Bool)
    (h : ∀ i<m,∀ b,c (i,b)=e (i,b)) : internalWord side m c=internalWord side m e := by
  induction m with
  | zero => rfl
  | succ m ih => simp [internalWord,h m (by omega),ih (fun i hi => h i (by omega))]
def edgeProduct (m : ℕ) (c : (ℕ × Bool) → Bool) : ℚ :=
  ∏ i : Fin m,Signature.disequality (c (i.val,false)) (c (i.val,true))
theorem edgeProduct_step (m : ℕ) (c : (ℕ × Bool) → Bool) :
    edgeProduct (m+1) c=edgeProduct m c*Signature.disequality (c (m,false)) (c (m,true)) := by
  exact Fin.prod_univ_castSucc _
theorem tree_weight (side : Bool) (m : ℕ) (w : List Bool) (hw : w.length=m+3)
    (c : (ℕ × Bool) → Bool) :
    rowsWeight w c (Layout.tree side m).vertices * edgeProduct m c=
      OldTree.weight (normalizedWord side w) (internalWord side m c) := by
  induction m generalizing w with
  | zero =>
      cases w with
      | nil => simp at hw
      | cons a w => cases w with
        | nil => simp at hw
        | cons b w => cases w with
          | nil => simp at hw
          | cons d tail =>
              have ht : tail=[] := List.eq_nil_of_length_eq_zero (by simp only [List.length_cons] at hw; omega)
              subst tail
              cases side <;> cases a <;> cases b <;> cases d <;> simp [Layout.tree,Layout.tag,rowsWeight,rowWeight,gate,slot,
                clause,TWO,one_ternary,OldTree.ternary,normalizedWord,normal,OldTree.weight,
                edgeProduct,internalWord,OldTree.tri,OldTree.bit]
  | succ m ih =>
      cases w with
      | nil => simp at hw
      | cons a w => cases w with
        | nil => simp at hw
        | cons b tail =>
            have hm : (c (m,false)::tail).length=m+3 := by
              simp only [List.length_cons] at hw ⊢
              omega
            have hr : rowsWeight (a::b::tail) c
                ((Layout.tree side m).vertices.map (fun r => (r.1,r.2.map (Layout.moved m))))=
                  rowsWeight (c (m,false)::tail) c (Layout.tree side m).vertices := by
              unfold rowsWeight
              simp only [List.map_map]
              apply congrArg List.prod
              apply List.map_congr_left
              intro r h
              exact row_moved m _ _ r (Layout.tree_labels side m r h).2
            simp only [Layout.tree,rowsWeight,List.map_append,List.prod_append,
              List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one]
            change rowsWeight (a::b::tail) c
              ((Layout.tree side m).vertices.map (fun r => (r.1,r.2.map (Layout.moved m)))) *
                rowWeight (a::b::tail) c (Layout.tag side,[.inl 0,.inl 1,.inr (m,true)]) *
                edgeProduct (m+1) c=_
            rw [hr,edgeProduct_step]
            rw [show rowsWeight (c (m,false)::tail) c (Layout.tree side m).vertices *
                rowWeight (a::b::tail) c (Layout.tag side,[.inl 0,.inl 1,.inr (m,true)]) *
                (edgeProduct m c*Signature.disequality (c (m,false)) (c (m,true)))=
              (rowsWeight (c (m,false)::tail) c (Layout.tree side m).vertices*edgeProduct m c)*
                (rowWeight (a::b::tail) c (Layout.tag side,[.inl 0,.inl 1,.inr (m,true)])*
                  Signature.disequality (c (m,false)) (c (m,true))) by ring]
            rw [ih _ hm]
            cases side <;>
              simp [rowWeight,slot,gate,Layout.tag,TWO,one_ternary,OldTree.ternary,
                OldTree.weight,internalWord,normal,normalizedWord,OldTree.tri,
                Signature.disequality,edge_both_complement] <;> ring

def packing (side : Bool) (m : ℕ) (z : (Fin m × Bool) → Bool) : Fin m → OldTree.Wire :=
  fun i => (normal side (z (i.rev,true)),normal side (z (i.rev,false)))
def packingEquiv (side : Bool) (m : ℕ) :
    ((Fin m × Bool) → Bool) ≃ (Fin m → OldTree.Wire) where
  toFun := packing side m
  invFun f p := normal side (if p.2 then (f p.1.rev).1 else (f p.1.rev).2)
  left_inv := by intro z; funext p; rcases p with ⟨i,b⟩; cases b <;> simp [packing]
  right_inv := by intro f; funext i; apply Prod.ext <;> simp [packing]
theorem packing_word (side : Bool) (m : ℕ) (z : (Fin m × Bool) → Bool) :
    List.ofFn (packing side m z)=internalWord side m (extend z) := by
  induction m with
  | zero => simp [internalWord]
  | succ m ih =>
      let old : (Fin m × Bool) → Bool := fun p => z (p.1.castSucc,p.2)
      have ht : (fun i : Fin m => packing side (m+1) z i.succ)=packing side m old := by
        funext i
        have he : i.succ.rev=i.rev.castSucc := Fin.rev_succ i
        simp [packing,old,he]
      have hh : packing side (m+1) z 0=
          (normal side (extend z (m,true)),normal side (extend z (m,false))) := by
        simp [packing,extend,Fin.rev]
      have hw : internalWord side m (extend old)=internalWord side m (extend z) := by
        apply internalWord_congr
        intro i hi b
        have hj : i<m+1 := by omega
        simp [old,extend,hi,hj]
      rw [List.ofFn_succ,ht,hh,ih old,hw,internalWord]
theorem tree_denote (side : Bool) (m : ℕ) (x : Fin (Layout.tree side m).boundary → Bool) :
    ((Layout.tree side m).network (Layout.tree_valid side m) palette edge).denote x=
      indicator side (List.ofFn x) := by
  rw [template_partition]
  unfold partition
  rw [(Layout.tree_counts side m).2.2]
  have hw : (List.ofFn x).length=m+3 := by simp [(Layout.tree_counts side m).1]
  have hterm (z : (Fin m × Bool) → Bool) :
      rowsWeight (List.ofFn x) (extend z) (Layout.tree side m).vertices *
        (∏ e : Fin m,Signature.disequality (z (e,false)) (z (e,true)))=
          OldTree.weight (normalizedWord side (List.ofFn x)) (List.ofFn (packing side m z)) := by
    rw [packing_word]
    simpa only [edgeProduct,extend_at] using tree_weight side m _ hw (extend z)
  simp_rw [hterm]
  exact ((packingEquiv side m).sum_comp
    (fun f => OldTree.weight (normalizedWord side (List.ofFn x)) (List.ofFn f))).trans
      (OldTree.local_partition_exact m _ (by simpa [normalizedWord] using hw))

private theorem one_layer : Signature.SingleLayer ONE 1 := by
  intro x hx
  simp only [Holant.weight,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero] at hx
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;>
    simp_all [ONE,OldTree.bit]

private theorem two_layer : Signature.SingleLayer TWO 2 := by
  intro x hx
  change ONE (fun i => !x i)=0
  apply one_layer
  have hw := Holant.weight_compl_add x
  omega

/-- The degree-zero template has total local charge ±2. Charge conservation
uses all actual native-X ends, including both ends of all three pad loops. -/
private theorem low_zero (side : Bool) : partition (Layout.low side 0) []=0 := by
  let G : Network ℚ 0 :=
    (Layout.low side 0).network (Layout.low_valid side 0 (by decide)) palette edge
  let layer : Fin G.shape.vertices → ℕ := fun v =>
    if v.val=0 then (if side then 2 else 1) else (if side then 1 else 2)
  have hlayer : ∀ v, Signature.SingleLayer (G.vertex v) (layer v) := by
    intro v
    change Fin 4 at v
    fin_cases v <;> cases side <;> first | exact one_layer | exact two_layer
  have imbalance : (∑ v : Fin G.shape.vertices, (2*(layer v : ℤ)-G.shape.arity v)) ≠ 0 := by
    change (∑ v : Fin 4,
      (2*((if v.val=0 then (if side then 2 else 1) else (if side then 1 else 2) : ℕ) : ℤ)-3)) ≠ 0
    cases side <;> norm_num [Fin.sum_univ_succ]
  have hzero := G.denote_eq_zero_of_singleLayer_imbalance (fun _ => rfl) layer hlayer imbalance
  have hv := congrFun hzero (Fin.elim0 : Fin 0 → Bool)
  change ((Layout.low side 0).network (Layout.low_valid side 0 (by decide)) palette edge).denote Fin.elim0=0 at hv
  rw [template_partition] at hv
  simpa using hv

/-- Exact low-degree tables. Degree zero follows from actual incidence charge;
the three remaining finite Boolean tables use kernel reduction, retaining both
ends of every physical padding loop. No native_decide or value-law input. -/
theorem low_partition (side : Bool) (d : ℕ) (hd : d≤3) (x : Fin d → Bool) :
    partition (Layout.low side d) (List.ofFn x)=
      (2 : ℚ)^(3-d)*indicator side (List.ofFn x) := by
  interval_cases d <;> cases side
  · simpa [indicator,normalizedWord] using low_zero false
  · simpa [indicator,normalizedWord] using low_zero true
  all_goals
    revert x
    decide +kernel

private theorem tuple_of_word (w : List Bool) (n : ℕ) (h : w.length=n) :
    ∃ x : Fin n → Bool,List.ofFn x=w := by
  subst n
  exact ⟨w.get,List.ofFn_get w⟩

theorem degree_denote (side : Bool) (d : ℕ) (x : Fin (Layout.degree side d).boundary → Bool) :
    ((Layout.degree side d).network (Layout.degree_valid side d) palette edge).denote x=
      (2 : ℚ)^(3-d)*indicator side (List.ofFn x) := by
  rw [template_partition]
  have hw : (List.ofFn x).length=d := by simp [Layout.degree_boundary]
  by_cases hd : d≤3
  · have ht : Layout.degree side d=Layout.low side d := by simp [Layout.degree,hd]
    obtain ⟨y,hy⟩ := tuple_of_word (List.ofFn x) d hw
    calc
      partition (Layout.degree side d) (List.ofFn x) =
          partition (Layout.low side d) (List.ofFn x) :=
        congrArg (fun T => partition T (List.ofFn x)) ht
      _ = (2 : ℚ)^(3-d)*indicator side (List.ofFn x) := by
        simpa only [hy] using low_partition side d hd y
  · have hp : 3-d=0 := by omega
    have ht : Layout.degree side d=Layout.tree side (d-3) := by simp [Layout.degree,hd]
    have hw' : (List.ofFn x).length=(Layout.tree side (d-3)).boundary := by
      rw [(Layout.tree_counts side (d-3)).1,hw]
      omega
    obtain ⟨y,hy⟩ := tuple_of_word (List.ofFn x) (Layout.tree side (d-3)).boundary hw'
    have htree := tree_denote side (d-3) y
    rw [template_partition] at htree
    calc
      partition (Layout.degree side d) (List.ofFn x) =
          partition (Layout.tree side (d-3)) (List.ofFn x) :=
        congrArg (fun T => partition T (List.ofFn x)) ht
      _ = indicator side (List.ofFn x) := by simpa only [hy] using htree
      _ = (2 : ℚ)^(3-d)*indicator side (List.ofFn x) := by simp [hp]

end Literal
end Holant.LocalDrafts.Hardness.EightVertexNonexception.SixVertexInterpolation.VerifierGates.NativeCubicMatching
