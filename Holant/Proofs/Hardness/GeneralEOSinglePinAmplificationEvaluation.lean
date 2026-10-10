import Holant.Proofs.Hardness.GeneralEOSinglePinAmplificationValidation
import Holant.Proofs.Hardness.GeneralEOSinglePinAmplificationColours
import Holant.Proofs.Hardness.ExactTwoReferenceEvaluation

/-! Exact partition value of the original-record DEQ4 amplifier. All original
weights remain in place; one actual anchor selects the desired reference phase.
This proves the value before any scalar normalization or oracle composition. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOSinglePinAmplificationEvaluation
open Holant Holant.Complexity FixedGadgetSubstitution UniversalPairReduction
open GeneralEOSinglePinAmplificationRaw GeneralEOSinglePinAmplificationValidation
open ExactTwoReferenceValidation (range_map_ofFn)
open ExactTwoReferenceEvaluation (joinColour joinEquiv extend_join_new bit_join_old
  weight_append weight_ofFn read4 read4_list)
open scoped BigOperators
namespace C
export ExactTwoReferenceColours (factor pinValue)
end C
namespace AC
export GeneralEOSinglePinAmplificationColours (anchor weight sum_colours)
end AC
namespace Choice
export UniversalPairReduction.Surgery.Choice (Table extend bit rowValue weight evaluate)
end Choice
set_option backward.isDefEq.respectTransparency false
variable {K : Type*} [Field K] {s j : ℕ} {a : ℕ → ℕ}

def sourceTable (s : ℕ) (F : Choice.Table K) : Choice.Table K := fun label bits =>
  if label<s then F label bits else C.pinValue false (bits.getD 0 false) (bits.getD 1 false)
theorem endpoint_lt {r : RawClosedNetwork} (hr : r.WellFormed (s+1) 1 (extendedArity s a))
    (p : RawEndpoint) (hp : p∈r.endpoints) : p.1<r.edges.length := by
  have hm := hr.2.2.mem_iff.mp hp
  rw [expectedEndpoints_eq] at hm
  obtain ⟨i,hi,hp⟩ := List.mem_flatMap.mp hm
  have hi' := List.mem_range.mp hi
  simp only [List.mem_cons,List.mem_nil_iff,or_false,Nat.zero_add] at hp
  rcases hp with rfl|rfl <;> exact hi'

theorem row_endpoint_lt {r : RawClosedNetwork} (hr : r.WellFormed (s+1) 1 (extendedArity s a))
    (v : RawVertex) (hv : v∈r.vertices) (p : RawEndpoint) (hp : p∈v.2) : p.1<r.edges.length :=
  endpoint_lt hr p (List.mem_flatten.mpr ⟨v.2,List.mem_map.mpr ⟨v,hv,rfl⟩,hp⟩)

def p0 (s : ℕ) (r : RawClosedNetwork) (i : Fin (count s r)) : RawEndpoint :=
  ((pinRows s r).getD i.val (0,[])).2.getD 0 (0,false)
def p1 (s : ℕ) (r : RawClosedNetwork) (i : Fin (count s r)) : RawEndpoint :=
  ((pinRows s r).getD i.val (0,[])).2.getD 1 (0,false)

def A (s : ℕ) (r : RawClosedNetwork) (c : ℕ → Bool) (i : Fin (count s r)) : Bool := Choice.bit c (p0 s r i)
def B (s : ℕ) (r : RawClosedNetwork) (c : ℕ → Bool) (i : Fin (count s r)) : Bool := Choice.bit c (p1 s r i)

theorem pin_mem (s : ℕ) (r : RawClosedNetwork) (i : Fin (count s r)) :
    (pinRows s r).getD i.val (0,[])∈pinRows s r := by
  rw [List.getD_eq_getElem _ _ i.isLt]
  exact List.getElem_mem i.isLt

theorem pin_label (s : ℕ) (r : RawClosedNetwork) (i : Fin (count s r)) :
    ((pinRows s r).getD i.val (0,[])).1=s := by
  have h := (List.mem_filter.mp (pin_mem s r i)).2
  simpa using h

theorem p0_lt {r : RawClosedNetwork} (hr : r.WellFormed (s+1) 1 (extendedArity s a)) (i : Fin (count s r)) :
    (p0 s r i).1<r.edges.length := by
  apply row_endpoint_lt hr _ (List.mem_filter.mp (pin_mem s r i)).1
  rw [pin_ports hr i.val i.isLt]
  exact List.mem_cons_self

theorem p1_lt {r : RawClosedNetwork} (hr : r.WellFormed (s+1) 1 (extendedArity s a)) (i : Fin (count s r)) :
    (p1 s r i).1<r.edges.length := by
  apply row_endpoint_lt hr _ (List.mem_filter.mp (pin_mem s r i)).1
  rw [pin_ports hr i.val i.isLt]
  exact List.mem_cons_of_mem _ (List.mem_singleton_self _)


theorem old_source (F : Choice.Table K) (r : RawClosedNetwork) (c : ℕ → Bool) :
    Choice.weight (sourceTable s F) c (oldRows s r)=Choice.weight F c (oldRows s r) := by
  unfold Choice.weight
  congr 1
  apply List.map_congr_left
  intro v hv
  have hl : v.1<s := of_decide_eq_true (List.mem_filter.mp hv).2
  simp only [Choice.rowValue,sourceTable,if_pos hl]

theorem pin_source {r : RawClosedNetwork} (hr : r.WellFormed (s+1) 1 (extendedArity s a))
    (F : Choice.Table K) (c : ℕ → Bool) (i : Fin (count s r)) :
    Choice.rowValue (sourceTable s F) c ((pinRows s r).getD i.val (0,[]))=
      C.pinValue false (A s r c i) (B s r c i) := by
  unfold Choice.rowValue
  rw [pin_label]
  simp only [sourceTable,lt_self_iff_false,ite_false]
  rw [pin_ports hr i.val i.isLt]
  rfl

theorem source_weight {r : RawClosedNetwork} (hr : r.WellFormed (s+1) 1 (extendedArity s a))
    (F : Choice.Table K) (c : ℕ → Bool) :
    Choice.weight (sourceTable s F) c r.vertices=
      Choice.weight F c (oldRows s r)*(∏i,C.pinValue false (A s r c i) (B s r c i)) := by
  rw [←UniversalPairReduction.Surgery.Choice.weight_perm (sourceTable s F) c (rows_partition hr)]
  rw [weight_append,old_source,weight_ofFn (sourceTable s F) c (pinRows s r)]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  exact pin_source hr F c i

theorem old_target_join {r : RawClosedNetwork} (hr : r.WellFormed (s+1) 1 (extendedArity s a))
    (F : Choice.Table K) (c : Fin r.edges.length → Bool) (y : Fin (count s r+1) → Bool) :
    Choice.weight (sourceTable s F) (Choice.extend (joinColour c y)) (oldRows s r)=
      Choice.weight F (Choice.extend c) (oldRows s r) := by
  unfold Choice.weight
  congr 1
  apply List.map_congr_left
  intro v hv
  obtain ⟨hmem,hl⟩ := List.mem_filter.mp hv
  have hl' : v.1<s := of_decide_eq_true hl
  simp only [Choice.rowValue,sourceTable,if_pos hl']
  apply congrArg (F v.1)
  apply List.map_congr_left
  intro p hp
  exact bit_join_old c y p (row_endpoint_lt hr v hmem p hp)

theorem ring_row {r : RawClosedNetwork} (hr : r.WellFormed (s+1) 1 (extendedArity s a))
    (F : Choice.Table K) (hj : j<s)
    (hE : ∀bits,F j bits=ExactTwoSignatures.E (read4 bits))
    (c : Fin r.edges.length → Bool) (y : Fin (count s r+1) → Bool)
    (i : Fin (count s r)) :
    Choice.rowValue (sourceTable s F) (Choice.extend (joinColour c y)) (row s j r i.val)=
      C.factor (A s r (Choice.extend c) i) (B s r (Choice.extend c) i)
        (y i.castSucc) (y i.succ) := by
  simp only [Choice.rowValue,sourceTable,row,if_pos hj,reference_succ,List.cons_append,
    List.nil_append,List.map_cons,List.map_nil,hE,read4_list]
  change ExactTwoSignatures.E ![Choice.bit _ (p0 s r i),Choice.bit _ (p1 s r i),_,_]=_
  rw [bit_join_old c y (p0 s r i) (p0_lt hr i),bit_join_old c y (p1 s r i) (p1_lt hr i)]
  simp only [Choice.bit]
  rw [extend_join_new c y (show i.val<count s r+1 by omega),
    show r.edges.length+i.val+1=r.edges.length+(i.val+1) by omega,
    extend_join_new c y (show i.val+1<count s r+1 by omega)]
  rfl

theorem anchor_row (F : Choice.Table K) (r : RawClosedNetwork)
    (c : Fin r.edges.length → Bool) (y : Fin (count s r+1) → Bool) :
    Choice.rowValue (sourceTable s F) (Choice.extend (joinColour c y)) (anchor s r)=
      AC.anchor (y (Fin.last (count s r))) (y 0) := by
  simp only [Choice.rowValue,sourceTable,anchor,lt_self_iff_false,ite_false,reference_zero,
    List.map_cons,List.map_nil,List.getD_cons_zero,List.getD_cons_succ]
  change C.pinValue false (Choice.bit _ (r.edges.length+count s r,true))
    (Choice.bit _ (r.edges.length,false))=_
  simp only [Choice.bit]
  rw [extend_join_new c y (Nat.lt_succ_self _)]
  have hz : Choice.extend (joinColour c y) r.edges.length=y 0 := by
    calc
      _ = y ⟨0,by omega⟩ := by
        simpa only [Nat.add_zero] using extend_join_new c y (show 0<count s r+1 by omega)
      _ = y 0 := congrArg y (Fin.ext (by simp))
  rw [hz]
  change C.pinValue false (y (Fin.last (count s r))) (!(y 0))=AC.anchor _ _
  cases h0 : y (Fin.last (count s r)) <;> cases h1 : y 0 <;> simp [C.pinValue,AC.anchor,h0,h1]

theorem target_weight {r : RawClosedNetwork} (hr : r.WellFormed (s+1) 1 (extendedArity s a))
    (F : Choice.Table K) (hj : j<s)
    (hE : ∀bits,F j bits=ExactTwoSignatures.E (read4 bits))
    (c : Fin r.edges.length → Bool) (y : Fin (count s r+1) → Bool) :
    Choice.weight (sourceTable s F) (Choice.extend (joinColour c y)) (raw s j r).vertices=
      Choice.weight F (Choice.extend c) (oldRows s r)*
        AC.weight (A s r (Choice.extend c)) (B s r (Choice.extend c)) y := by
  rw [show (raw s j r).vertices=oldRows s r++anchor s r::rows s j r from rfl,
    weight_append,old_target_join hr F c y]
  congr 1
  change Choice.rowValue (sourceTable s F) (Choice.extend (joinColour c y)) (anchor s r)*
      Choice.weight (sourceTable s F) (Choice.extend (joinColour c y)) (rows s j r)=_
  rw [anchor_row]
  unfold AC.weight
  congr 1
  simp only [Choice.weight,rows,List.map_map,Function.comp_def]
  rw [range_map_ofFn,List.prod_ofFn]
  apply Finset.prod_congr rfl
  intro i _
  exact ring_row hr F hj hE c y i

theorem value {r : RawClosedNetwork} (hr : r.WellFormed (s+1) 1 (extendedArity s a))
    (F : Choice.Table K) (hj : j<s)
    (hE : ∀bits,F j bits=ExactTwoSignatures.E (read4 bits)) :
    Choice.evaluate (sourceTable s F) (raw s j r).edges.length (raw s j r).vertices=
      Choice.evaluate (sourceTable s F) r.edges.length r.vertices := by
  rw [edges_length,show r.edges.length+count s r+1=r.edges.length+(count s r+1) by omega]
  change (∑z : Fin (r.edges.length+(count s r+1)) → Bool,
    Choice.weight (sourceTable s F) (Choice.extend z) (raw s j r).vertices)=_
  calc
    _ = ∑p : (Fin r.edges.length → Bool)×(Fin (count s r+1) → Bool),
        Choice.weight (sourceTable s F) (Choice.extend (joinColour p.1 p.2)) (raw s j r).vertices := by
      symm
      apply Fintype.sum_equiv (joinEquiv r.edges.length (count s r+1))
      intro p
      rfl
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro c _
      simp_rw [target_weight hr F hj hE]
      rw [←Finset.mul_sum,AC.sum_colours,source_weight hr F]

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOSinglePinAmplificationEvaluation
