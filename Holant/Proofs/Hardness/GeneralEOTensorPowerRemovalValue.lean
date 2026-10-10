import Holant.Proofs.Hardness.GeneralEOTensorPowerRemovalRaw
import Holant.Complexity.UniversalPairReduction.Surgery.ChoiceSemantics

/-! Assignment-by-assignment tensor grouping, followed by the complete native-X
partition sum. Every source row is retained exactly once in the product; grouping
creates no edge assignment and hence introduces no scalar or free-variable factor.
The row-table presentation is total even on malformed records. -/
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOTensorPowerRemovalValue
open Holant Holant.Complexity GeneralEOTensorPowerRemovalRaw
open UniversalPairReduction.Surgery
open scoped BigOperators
variable {K : Type*} [CommSemiring K]

/-- Copy-major tensor product on the actual ordered bit list. -/
def tensorList (n : ℕ) (f : List Bool→K) : ℕ→List Bool→K
  | 0, _ => 1
  | k+1, bs => f (bs.take n)*tensorList n f k (bs.drop n)

def sourceTable (s : ℕ) (F : Choice.Table K) (f : List Bool→K) : Choice.Table K :=
  fun i bs=>if i<s then F i bs else f bs

def targetTable (s n k : ℕ) (F : Choice.Table K) (f : List Bool→K) : Choice.Table K :=
  sourceTable s F (tensorList n f k)

@[simp] theorem tensorList_zero (n : ℕ) (f : List Bool→K) (bs : List Bool) :
    tensorList n f 0 bs=1 := rfl

theorem tensorList_append (n k : ℕ) (f : List Bool→K) (bs cs : List Bool)
    (h : bs.length=n) : tensorList n f (k+1) (bs++cs)=f bs*tensorList n f k cs := by
  subst n
  simp [tensorList]

theorem tensorList_rows (n : ℕ) (f : List Bool→K) (c : RawEndpoint→Bool)
    (rows : List RawVertex) (h : ∀v∈rows,v.2.length=n) :
    tensorList n f rows.length ((rows.flatMap Prod.snd).map c)=
      (rows.map (fun v=>f (v.2.map c))).prod := by
  induction rows with
  | nil => rfl
  | cons v rows ih =>
    have hv : (v.2.map c).length=n := by simpa using h v (by simp)
    have ht := ih (fun w hw=>h w (by simp [hw]))
    simp only [List.length_cons,List.flatMap_cons,List.map_append,tensorList_append n _ f _ _ hv,
      List.map_cons,List.prod_cons,ht]

theorem groupedRow_value {s b n : ℕ} {a : ℕ→ℕ} {r : RawClosedNetwork}
    (hr : r.WellFormed (s+1) b (sourceArity s n a))
    (F : Choice.Table K) (f : List Bool→K) (c : ℕ→Bool)
    (rows : List RawVertex) (h : ∀v∈rows,v∈selected s r) :
    Choice.rowValue (targetTable s n rows.length F f) c (groupedRow s rows)=
      Choice.weight (sourceTable s F f) c rows := by
  have hp := tensorList_rows n f (Choice.bit c) rows (fun v hv=>(selected_valid hr v (h v hv)).2)
  simp only [Choice.rowValue,targetTable,sourceTable,groupedRow,lt_self_iff_false,ite_false]
  rw [hp]
  unfold Choice.weight
  congr 1
  apply List.map_congr_left
  intro v hv
  have hs := (selected_valid hr v (h v hv)).1
  simp [Choice.rowValue,sourceTable,hs]

theorem weight_append (F : Choice.Table K) (c : ℕ→Bool) (xs ys : List RawVertex) :
    Choice.weight F c (xs++ys)=Choice.weight F c xs*Choice.weight F c ys := by
  simp [Choice.weight]

theorem weight_flatten (F : Choice.Table K) (c : ℕ→Bool) (xss : List (List RawVertex)) :
    (xss.map (Choice.weight F c)).prod=Choice.weight F c xss.flatten := by
  induction xss with
  | nil => rfl
  | cons xs xss ih => simp only [List.map_cons,List.prod_cons,List.flatten_cons,weight_append,ih]

/-- One grouped row evaluates to the product of its actual k original rows. -/
theorem grouped_weight {s b n k : ℕ} {a : ℕ→ℕ} {r : RawClosedNetwork}
    (hr : r.WellFormed (s+1) b (sourceArity s n a)) (h : count s r%k=0)
    (F : Choice.Table K) (f : List Bool→K) (c : ℕ→Bool) :
    Choice.weight (targetTable s n k F f) c (groupedRows s k r)=
      Choice.weight (sourceTable s F f) c (selected s r) := by
  have hm := count_eq_mul h
  unfold groupedRows Choice.weight
  rw [List.map_map]
  have he : (blocks k (count s r/k) (selected s r)).map
      (fun rows=>Choice.rowValue (targetTable s n k F f) c (groupedRow s rows))=
      (blocks k (count s r/k) (selected s r)).map (Choice.weight (sourceTable s F f) c) := by
    apply List.map_congr_left
    intro rows hrows
    have hl := blocks_member_length k (count s r/k) (selected s r) hm rows hrows
    rw [←hl]
    exact groupedRow_value hr F f c rows (fun v hv=>blocks_member k _ _ hm hrows hv)
  change (List.map (fun rows=>Choice.rowValue (targetTable s n k F f) c (groupedRow s rows)) _).prod=_
  rw [he,weight_flatten,blocks_flatten k _ _ hm]
  rfl

/-- Pointwise preservation holds before summing any assignment. -/
theorem weight_eq {s b n k : ℕ} {a : ℕ→ℕ} {r : RawClosedNetwork}
    (hr : r.WellFormed (s+1) b (sourceArity s n a)) (h : count s r%k=0)
    (F : Choice.Table K) (f : List Bool→K) (c : ℕ→Bool) :
    Choice.weight (targetTable s n k F f) c (raw s k r).vertices=
      Choice.weight (sourceTable s F f) c r.vertices := by
  have ho : Choice.weight (targetTable s n k F f) c (oldRows s r)=
      Choice.weight (sourceTable s F f) c (oldRows s r) := by
    unfold Choice.weight
    congr 1
    apply List.map_congr_left
    intro v hv
    have hh : v.1<s := of_decide_eq_true (List.mem_filter.mp hv).2
    simp [Choice.rowValue,targetTable,sourceTable,hh]
  change Choice.weight _ c (oldRows s r++groupedRows s k r)=_
  rw [weight_append,ho,grouped_weight hr h F f c,←weight_append]
  exact Choice.weight_perm _ _ (rows_partition s r.vertices (fun v hv=>(row_valid hr v hv).1))

/-- Exact full partition value, with unchanged edge count and scalar one. -/
theorem evaluate_eq {s b n k : ℕ} {a : ℕ→ℕ} {r : RawClosedNetwork}
    (hr : r.WellFormed (s+1) b (sourceArity s n a)) (h : count s r%k=0)
    (F : Choice.Table K) (f : List Bool→K) :
    Choice.evaluate (targetTable s n k F f) (raw s k r).edges.length (raw s k r).vertices=
      Choice.evaluate (sourceTable s F f) r.edges.length r.vertices := by
  unfold Choice.evaluate
  apply Finset.sum_congr rfl
  intro c _
  exact weight_eq hr h F f (Choice.extend c)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOTensorPowerRemovalValue
