import Holant.Proofs.Hardness.ExactTwoReferenceColours
import Holant.Complexity.UniversalPairReduction.Surgery.ChoiceSemantics

/-! Exact raw native-X partition surgery. Old edge colours
and fresh reference colours are separated by an explicit finite bijection.
Every old ordered endpoint is evaluated at its unchanged original edge colour. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.ExactTwoReferenceEvaluation
open Holant Holant.Complexity FixedGadgetSubstitution
open ExactTwoReferenceRaw ExactTwoReferenceValidation
open scoped BigOperators
namespace C
export ExactTwoReferenceColours (factor pinValue weight sum_colours sum_empty)
end C
namespace Choice
export UniversalPairReduction.Surgery.Choice (Table extend bit rowValue weight evaluate)
end Choice
set_option backward.isDefEq.respectTransparency false
variable {K : Type*} [Field K]

def read4 (bits : List Bool) : Fin 4 → Bool := fun i=>bits.getD i.val false

def oldTable (q : Signature K 4) : Choice.Table K := fun _ bits=>q (read4 bits)
def sourceTable (q : Signature K 4) (phase : Bool) : Choice.Table K := fun label bits=>
  if label<1 then q (read4 bits) else C.pinValue phase (bits.getD 0 false) (bits.getD 1 false)
def targetTable (q : Signature K 4) : Choice.Table K := fun label bits=>
  if label<1 then q (read4 bits) else ExactTwoSignatures.E (read4 bits)

def joinColour {e m : ℕ} (c : Fin e → Bool) (y : Fin m → Bool) (i : Fin (e+m)) : Bool :=
  if h : i.val<e then c ⟨i.val,h⟩ else y ⟨i.val-e,by omega⟩

def joinEquiv (e m : ℕ) : ((Fin e → Bool)×(Fin m → Bool)) ≃ (Fin (e+m) → Bool) where
  toFun p := joinColour p.1 p.2
  invFun z := (fun i=>z (i.castAdd m),fun i=>z (i.natAdd e))
  left_inv p := by
    apply Prod.ext
    · funext i
      simp only [joinColour,Fin.val_castAdd,dif_pos i.isLt]
    · funext i
      have hn : ¬e+i.val<e := by omega
      simp only [joinColour,Fin.val_natAdd,dif_neg hn,Nat.add_sub_cancel_left]
  right_inv z := by
    funext i
    change (if h : i.val<e then z (Fin.castAdd m ⟨i.val,h⟩)
      else z (Fin.natAdd e ⟨i.val-e,by omega⟩))=z i
    split_ifs with hi
    · rfl
    · congr 1
      apply Fin.ext
      simp only [Fin.val_natAdd]
      omega

theorem extend_join_old {e m i : ℕ} (c : Fin e → Bool) (y : Fin m → Bool) (hi : i<e) :
    Choice.extend (joinColour c y) i=Choice.extend c i := by
  have hs : i<e+m := by omega
  simp only [Choice.extend,dif_pos hi,dif_pos hs,joinColour]

theorem extend_join_new {e m i : ℕ} (c : Fin e → Bool) (y : Fin m → Bool) (hi : i<m) :
    Choice.extend (joinColour c y) (e+i)=y ⟨i,hi⟩ := by
  have hs : e+i<e+m := by omega
  have hn : ¬e+i<e := by omega
  simp only [Choice.extend,dif_pos hs,joinColour,dif_neg hn,Nat.add_sub_cancel_left]

theorem bit_join_old {e m : ℕ} (c : Fin e → Bool) (y : Fin m → Bool)
    (p : RawEndpoint) (hp : p.1<e) :
    Choice.bit (Choice.extend (joinColour c y)) p=Choice.bit (Choice.extend c) p := by
  unfold Choice.bit
  rw [extend_join_old c y hp]

theorem endpoint_lt {r : RawClosedNetwork} (hr : r.WellFormed 2 1 sourceArity)
    (p : RawEndpoint) (hp : p∈r.endpoints) : p.1<r.edges.length := by
  have hm := hr.2.2.mem_iff.mp hp
  rw [expectedEndpoints_eq] at hm
  obtain ⟨i,hi,hp⟩ := List.mem_flatMap.mp hm
  have hi' := List.mem_range.mp hi
  simp only [List.mem_cons,List.mem_nil_iff,or_false,Nat.zero_add] at hp
  rcases hp with rfl|rfl <;> exact hi'

theorem row_endpoint_lt {r : RawClosedNetwork} (hr : r.WellFormed 2 1 sourceArity)
    (v : RawVertex) (hv : v∈r.vertices) (p : RawEndpoint) (hp : p∈v.2) : p.1<r.edges.length :=
  endpoint_lt hr p (List.mem_flatten.mpr ⟨v.2,List.mem_map.mpr ⟨v,hv,rfl⟩,hp⟩)

def p0 (r : RawClosedNetwork) (i : Fin (count r)) : RawEndpoint :=
  ((pinRows r).getD i.val (0,[])).2.getD 0 (0,false)
def p1 (r : RawClosedNetwork) (i : Fin (count r)) : RawEndpoint :=
  ((pinRows r).getD i.val (0,[])).2.getD 1 (0,false)

def A (r : RawClosedNetwork) (c : ℕ → Bool) (i : Fin (count r)) : Bool := Choice.bit c (p0 r i)
def B (r : RawClosedNetwork) (c : ℕ → Bool) (i : Fin (count r)) : Bool := Choice.bit c (p1 r i)

theorem pin_mem (r : RawClosedNetwork) (i : Fin (count r)) :
    (pinRows r).getD i.val (0,[])∈pinRows r := by
  rw [List.getD_eq_getElem _ _ i.isLt]
  exact List.getElem_mem i.isLt

theorem pin_label (r : RawClosedNetwork) (i : Fin (count r)) :
    ((pinRows r).getD i.val (0,[])).1=1 := by
  have h := (List.mem_filter.mp (pin_mem r i)).2
  simpa using h

theorem p0_lt {r : RawClosedNetwork} (hr : r.WellFormed 2 1 sourceArity) (i : Fin (count r)) :
    (p0 r i).1<r.edges.length := by
  apply row_endpoint_lt hr _ (List.mem_filter.mp (pin_mem r i)).1
  rw [pin_ports hr i.val i.isLt]
  exact List.mem_cons_self

theorem p1_lt {r : RawClosedNetwork} (hr : r.WellFormed 2 1 sourceArity) (i : Fin (count r)) :
    (p1 r i).1<r.edges.length := by
  apply row_endpoint_lt hr _ (List.mem_filter.mp (pin_mem r i)).1
  rw [pin_ports hr i.val i.isLt]
  exact List.mem_cons_of_mem _ (List.mem_singleton_self _)

 theorem weight_append (F : Choice.Table K) (c : ℕ → Bool) (xs ys : List RawVertex) :
    Choice.weight F c (xs++ys)=Choice.weight F c xs*Choice.weight F c ys := by
  simp only [Choice.weight,List.map_append,List.prod_append]

 theorem weight_ofFn (F : Choice.Table K) (c : ℕ → Bool) (xs : List RawVertex) :
    Choice.weight F c xs=∏i : Fin xs.length,Choice.rowValue F c (xs.getD i.val (0,[])) := by
  unfold Choice.weight
  rw [←List.ofFn_getElem_eq_map xs (Choice.rowValue F c),List.prod_ofFn]
  apply Finset.prod_congr rfl
  intro i _
  rw [List.getD_eq_getElem _ _ i.isLt]

 theorem old_source (q : Signature K 4) (phase : Bool) (r : RawClosedNetwork) (c : ℕ → Bool) :
    Choice.weight (sourceTable q phase) c (oldRows r)=Choice.weight (oldTable q) c (oldRows r) := by
  unfold Choice.weight
  congr 1
  apply List.map_congr_left
  intro v hv
  have hl : v.1<1 := of_decide_eq_true (List.mem_filter.mp hv).2
  simp only [Choice.rowValue,sourceTable,oldTable,if_pos hl]

 theorem pin_source {r : RawClosedNetwork} (hr : r.WellFormed 2 1 sourceArity)
    (q : Signature K 4) (phase : Bool) (c : ℕ → Bool) (i : Fin (count r)) :
    Choice.rowValue (sourceTable q phase) c ((pinRows r).getD i.val (0,[]))=
      C.pinValue phase (A r c i) (B r c i) := by
  unfold Choice.rowValue
  rw [pin_label]
  simp only [sourceTable,lt_self_iff_false,ite_false]
  rw [pin_ports hr i.val i.isLt]
  rfl

 theorem source_weight {r : RawClosedNetwork} (hr : r.WellFormed 2 1 sourceArity)
    (q : Signature K 4) (phase : Bool) (c : ℕ → Bool) :
    Choice.weight (sourceTable q phase) c r.vertices=
      Choice.weight (oldTable q) c (oldRows r)*(∏i,C.pinValue phase (A r c i) (B r c i)) := by
  rw [←UniversalPairReduction.Surgery.Choice.weight_perm (sourceTable q phase) c (rows_partition hr)]
  rw [weight_append,old_source,weight_ofFn (sourceTable q phase) c (pinRows r)]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  exact pin_source hr q phase c i

 theorem old_target_join {r : RawClosedNetwork} (hr : r.WellFormed 2 1 sourceArity)
    (q : Signature K 4) (c : Fin r.edges.length → Bool) (y : Fin (count r) → Bool) :
    Choice.weight (targetTable q) (Choice.extend (joinColour c y)) (oldRows r)=
      Choice.weight (oldTable q) (Choice.extend c) (oldRows r) := by
  unfold Choice.weight
  congr 1
  apply List.map_congr_left
  intro v hv
  obtain ⟨hmem,hl⟩ := List.mem_filter.mp hv
  have hl' : v.1<1 := of_decide_eq_true hl
  simp only [Choice.rowValue,targetTable,oldTable,if_pos hl']
  apply congrArg q
  apply congrArg read4
  apply List.map_congr_left
  intro p hp
  exact bit_join_old c y p (row_endpoint_lt hr v hmem p hp)

 theorem read4_list (a b c d : Bool) : read4 [a,b,c,d]=![a,b,c,d] := by
  funext i
  fin_cases i <;> rfl

 theorem ring_row {r : RawClosedNetwork} (hr : r.WellFormed 2 1 sourceArity)
    (q : Signature K 4) (c : Fin r.edges.length → Bool) (y : Fin (count r) → Bool)
    (i : Fin (count r)) :
    Choice.rowValue (targetTable q) (Choice.extend (joinColour c y)) (row r i.val)=
      C.factor (A r (Choice.extend c) i) (B r (Choice.extend c) i)
        (y (previousFin i)) (y i) := by
  simp only [Choice.rowValue,targetTable,row,lt_self_iff_false,ite_false,List.map_cons,List.map_nil,read4_list]
  change ExactTwoSignatures.E ![Choice.bit _ (p0 r i),Choice.bit _ (p1 r i),_,_]=_
  rw [bit_join_old c y (p0 r i) (p0_lt hr i),bit_join_old c y (p1 r i) (p1_lt hr i)]
  simp only [Choice.bit]
  rw [extend_join_new c y (previous_lt i.isLt),extend_join_new c y i.isLt]
  rfl

 theorem target_weight {r : RawClosedNetwork} (hr : r.WellFormed 2 1 sourceArity)
    (q : Signature K 4) (c : Fin r.edges.length → Bool) (y : Fin (count r) → Bool) :
    Choice.weight (targetTable q) (Choice.extend (joinColour c y)) (raw r).vertices=
      Choice.weight (oldTable q) (Choice.extend c) (oldRows r)*
        C.weight (A r (Choice.extend c)) (B r (Choice.extend c)) y := by
  rw [show (raw r).vertices=oldRows r++rows r from rfl,weight_append,old_target_join hr q c y]
  congr 1
  simp only [Choice.weight,rows,List.map_map,Function.comp_def]
  rw [range_map_ofFn,List.prod_ofFn]
  apply Finset.prod_congr rfl
  intro i _
  exact ring_row hr q c y i

 theorem separated_sum {r : RawClosedNetwork} (hr : r.WellFormed 2 1 sourceArity)
    (q : Signature K 4) :
    Choice.evaluate (targetTable q) (raw r).edges.length (raw r).vertices=
      ∑c : Fin r.edges.length → Bool,
        Choice.weight (oldTable q) (Choice.extend c) (oldRows r)*
          ∑y : Fin (count r) → Bool,C.weight (A r (Choice.extend c)) (B r (Choice.extend c)) y := by
  rw [edges_length]
  change (∑z : Fin (r.edges.length+count r) → Bool,
    Choice.weight (targetTable q) (Choice.extend z) (raw r).vertices)=_
  calc
    _ = ∑p : (Fin r.edges.length → Bool)×(Fin (count r) → Bool),
        Choice.weight (targetTable q) (Choice.extend (joinColour p.1 p.2)) (raw r).vertices := by
      symm
      apply Fintype.sum_equiv (joinEquiv r.edges.length (count r))
      intro p
      rfl
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro c _
      simp_rw [target_weight hr q]
      rw [Finset.mul_sum]

 theorem branch_sum {r : RawClosedNetwork} (hr : r.WellFormed 2 1 sourceArity)
    (hm : 0<count r) (q : Signature K 4) :
    Choice.evaluate (targetTable q) (raw r).edges.length (raw r).vertices=
      Choice.evaluate (sourceTable q false) r.edges.length r.vertices+
        Choice.evaluate (sourceTable q true) r.edges.length r.vertices := by
  rw [separated_sum hr q]
  simp_rw [C.sum_colours hm]
  simp_rw [mul_add,←source_weight hr q]
  exact Finset.sum_add_distrib

 theorem zero_value {r : RawClosedNetwork} (hr : r.WellFormed 2 1 sourceArity)
    (hm : count r=0) (q : Signature K 4) :
    Choice.evaluate (targetTable q) (raw r).edges.length (raw r).vertices=
      Choice.evaluate (sourceTable q false) r.edges.length r.vertices := by
  rw [separated_sum hr q]
  unfold Choice.evaluate
  apply Finset.sum_congr rfl
  intro c _
  rw [source_weight hr q]
  have hp : (∏i : Fin (count r),C.pinValue (K:=K) false (A r (Choice.extend c) i) (B r (Choice.extend c) i))=1 := by
    apply Finset.prod_eq_one
    intro i _
    have hi := i.isLt
    omega
  rw [hp]
  congr 1
  have hz : ∀ (n : ℕ) (a b : Fin n → Bool),n=0 →
      (∑y : Fin n → Bool,C.weight (K:=K) a b y)=1 := by
    intro n a b hn
    subst n
    exact C.sum_empty a b
  exact hz (count r) (A r (Choice.extend c)) (B r (Choice.extend c)) hm

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.ExactTwoReferenceEvaluation
