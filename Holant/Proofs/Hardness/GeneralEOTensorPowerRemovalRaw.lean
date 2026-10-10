import Holant.Complexity.ClosedNetworkSemantics
import Holant.Complexity.FixedGadgetSubstitution.Raw

/-! Literal fixed tensor-power grouping. The distinguished final source label
is read from the actual row stream. Consecutive blocks of k selected rows are
replaced by one row whose ordered ports are their concatenation. Original edge
IDs and both oriented ends of every loop are retained. No grouping or target
validity certificate is supplied to the algorithm. -/
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOTensorPowerRemovalRaw
open Holant.Complexity RawClosedNetwork

/-- A bounded, executable take/drop traversal, also defined on malformed data. -/
def blocks {α : Type*} (k : ℕ) : ℕ → List α → List (List α)
  | 0, _ => []
  | q+1, xs => xs.take k :: blocks k q (xs.drop k)

@[simp] theorem blocks_length {α : Type*} (k q : ℕ) (xs : List α) :
    (blocks k q xs).length=q := by induction q generalizing xs <;> simp [blocks, *]

theorem blocks_flatten {α : Type*} (k q : ℕ) (xs : List α) (h : xs.length=k*q) :
    (blocks k q xs).flatten=xs := by
  induction q generalizing xs with
  | zero =>
    have hx : xs=[] := List.length_eq_zero_iff.mp (by simpa using h)
    simp [blocks,hx]
  | succ q ih =>
    rw [Nat.mul_succ] at h
    have hd : (xs.drop k).length=k*q := by simp only [List.length_drop]; omega
    simp only [blocks,List.flatten_cons,ih _ hd,List.take_append_drop]

theorem blocks_member_length {α : Type*} (k q : ℕ) (xs : List α)
    (h : xs.length=k*q) (ys : List α) (hy : ys∈blocks k q xs) : ys.length=k := by
  induction q generalizing xs with
  | zero => simp [blocks] at hy
  | succ q ih =>
    rw [Nat.mul_succ] at h
    have hk : k≤xs.length := by omega
    have hd : (xs.drop k).length=k*q := by simp only [List.length_drop]; omega
    rcases List.mem_cons.mp hy with rfl|hy
    · exact List.length_take_of_le hk
    · exact ih _ hd hy

theorem blocks_member {α : Type*} (k q : ℕ) (xs : List α)
    (h : xs.length=k*q) {ys : List α} (hy : ys∈blocks k q xs) {x : α} (hx : x∈ys) : x∈xs := by
  rw [←blocks_flatten k q xs h]
  exact List.mem_flatten.mpr ⟨ys,hy,hx⟩

def sourceArity (s n : ℕ) (a : ℕ→ℕ) (i : ℕ) : ℕ := if i<s then a i else n

def targetArity (s n k : ℕ) (a : ℕ→ℕ) (i : ℕ) : ℕ := if i<s then a i else k*n

def oldRows (s : ℕ) (r : RawClosedNetwork) := r.vertices.filter (fun v=>v.1<s)
def selected (s : ℕ) (r : RawClosedNetwork) := r.vertices.filter (fun v=>v.1=s)
def count (s : ℕ) (r : RawClosedNetwork) := (selected s r).length

def groupedRow (s : ℕ) (rows : List RawVertex) : RawVertex := (s,rows.flatMap Prod.snd)

def groupedRows (s k : ℕ) (r : RawClosedNetwork) : List RawVertex :=
  (blocks k (count s r/k) (selected s r)).map (groupedRow s)

def raw (s k : ℕ) (r : RawClosedNetwork) : RawClosedNetwork :=
  ⟨oldRows s r++groupedRows s k r,r.edges⟩

@[simp] theorem raw_edges (s k : ℕ) (r : RawClosedNetwork) : (raw s k r).edges=r.edges := rfl

@[simp] theorem groupedRows_length (s k : ℕ) (r : RawClosedNetwork) :
    (groupedRows s k r).length=count s r/k := by simp [groupedRows]

theorem rows_partition (s : ℕ) (xs : List RawVertex) (h : ∀v∈xs,v.1<s+1) :
    ((xs.filter (fun v=>v.1<s))++(xs.filter (fun v=>v.1=s))).Perm xs := by
  induction xs with
  | nil => simp
  | cons v xs ih =>
    have hv := h v (by simp)
    have H := ih (fun w hw=>h w (by simp [hw]))
    by_cases ho : v.1<s
    · have hn : v.1≠s := by omega
      simpa [ho,hn] using H.cons v
    · have he : v.1=s := by omega
      simp [he]
      exact List.perm_middle.trans (H.cons v)

theorem row_valid {s b n : ℕ} {a : ℕ→ℕ} {r : RawClosedNetwork}
    (hr : r.WellFormed (s+1) b (sourceArity s n a)) (v : RawVertex) (hv : v∈r.vertices) :
    v.1<s+1 ∧ v.2.length=sourceArity s n a v.1 := by
  obtain ⟨j,rfl⟩ := List.mem_iff_get.mp hv
  exact hr.1 j

theorem selected_valid {s b n : ℕ} {a : ℕ→ℕ} {r : RawClosedNetwork}
    (hr : r.WellFormed (s+1) b (sourceArity s n a)) (v : RawVertex) (hv : v∈selected s r) :
    v.1=s ∧ v.2.length=n := by
  obtain ⟨hm,he⟩ := List.mem_filter.mp hv
  have he' : v.1=s := of_decide_eq_true he
  refine ⟨he',?_⟩
  simpa [sourceArity,he'] using (row_valid hr v hm).2

theorem flatMap_ports_length (rows : List RawVertex) (n : ℕ)
    (h : ∀v∈rows,v.2.length=n) : (rows.flatMap Prod.snd).length=rows.length*n := by
  induction rows with
  | nil => simp
  | cons v rows ih =>
    have hv := h v (by simp)
    have ht := ih (fun w hw=>h w (by simp [hw]))
    simp only [List.flatMap_cons,List.length_append,List.length_cons,hv,ht,Nat.add_mul,Nat.one_mul]
    omega

theorem count_eq_mul {s k : ℕ} {r : RawClosedNetwork} (h : count s r%k=0) :
    count s r=k*(count s r/k) := by
  have hh := Nat.mod_add_div (count s r) k
  omega

/-- Literal selected rows, including nullary rows, are partitioned exactly once. -/
theorem grouped_endpoints (s k : ℕ) (r : RawClosedNetwork) (h : count s r%k=0) :
    (groupedRows s k r).flatMap Prod.snd=(selected s r).flatMap Prod.snd := by
  have hh := congrArg (List.flatMap Prod.snd)
    (blocks_flatten k (count s r/k) (selected s r) (count_eq_mul h))
  simpa only [groupedRows,List.flatMap_map,groupedRow,List.flatten_eq_flatMap,List.flatMap_assoc,id_eq,Function.comp_def] using hh

/-- Graph surgery preserves the entire endpoint multiset. -/
theorem endpoints_perm {s b n k : ℕ} {a : ℕ→ℕ} {r : RawClosedNetwork}
    (hr : r.WellFormed (s+1) b (sourceArity s n a)) (h : count s r%k=0) :
    (raw s k r).endpoints.Perm r.endpoints := by
  have hp := (rows_partition s r.vertices (fun v hv=>(row_valid hr v hv).1)).flatMap_right Prod.snd
  simpa only [raw,endpoints,←List.flatMap_def,List.flatMap_append,grouped_endpoints s k r h,
    oldRows,selected] using hp

/-- The validator is derived from original validity and actual occurrence
arithmetic, including the zero-occurrence and empty-instance cases. -/
theorem wellFormed {s b n k : ℕ} {a : ℕ→ℕ} {r : RawClosedNetwork}
    (hr : r.WellFormed (s+1) b (sourceArity s n a)) (h : count s r%k=0) :
    (raw s k r).WellFormed (s+1) b (targetArity s n k a) := by
  refine ⟨?_,hr.2.1,(endpoints_perm hr h).trans hr.2.2⟩
  intro v
  have hm := List.get_mem (raw s k r).vertices v
  rcases List.mem_append.mp hm with ho|hg
  · obtain ⟨hv,hlt⟩ := List.mem_filter.mp ho
    have hlt' : ((raw s k r).vertices.get v).1<s := of_decide_eq_true hlt
    have H := row_valid hr _ hv
    exact ⟨H.1,by simpa only [sourceArity,targetArity,ite_eq_left hlt'] using H.2⟩
  · obtain ⟨ys,hy,he⟩ := List.mem_map.mp hg
    rw [←he]
    refine ⟨by simp [groupedRow],?_⟩
    have hl := blocks_member_length k (count s r/k) (selected s r) (count_eq_mul h) ys hy
    have hrows : ∀w∈ys,w.2.length=n := by
      intro w hw
      exact (selected_valid hr w (blocks_member k _ _ (count_eq_mul h) hy hw)).2
    simpa only [groupedRow,targetArity,lt_self_iff_false,ite_false,hl] using
      flatMap_ports_length ys n hrows

/-- Exact vertex balance: k old f rows are replaced by one tensor row. -/
theorem vertex_balance {s b n k : ℕ} {a : ℕ→ℕ} {r : RawClosedNetwork}
    (hr : r.WellFormed (s+1) b (sourceArity s n a)) :
    (raw s k r).vertices.length+count s r=r.vertices.length+count s r/k := by
  have hp := (rows_partition s r.vertices (fun v hv=>(row_valid hr v hv).1)).length_eq
  simp only [List.length_append] at hp
  simp only [raw,List.length_append,groupedRows_length,oldRows,count,selected]
  omega

/-- Counting is charged to the original faithful serialization. -/
theorem count_le_encoded_length (s : ℕ) (r : RawClosedNetwork) :
    count s r≤(RawClosedNetwork.encoding.encode r).length := by
  have h := List.length_filter_le (fun v : RawVertex=>decide (v.1=s)) r.vertices
  have hh := r.counts_le_encoded_length
  change (r.vertices.filter (fun v=>v.1=s)).length≤_ at h ⊢
  omega

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOTensorPowerRemovalRaw
