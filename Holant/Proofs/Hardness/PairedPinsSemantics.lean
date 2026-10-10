import Holant.Proofs.Hardness.PairedPinsRaw
import Holant.Complexity.ClosedNetworkSemantics

/-! Actual ordered regrouping of complementary unary occurrences. The raw
algorithm keeps every edge and combines the i-th zero-pin incidence with the
i-th one-pin incidence. No new edge, scalar, assignment or free pin is added.
The validator and full weighted native-X semantics are proved separately. -/
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.PairedPinsSemantics
open Holant Holant.Complexity PairedPinsRaw
open scoped BigOperators

/-- A three-way stable partition, retaining all row multiplicities. -/
theorem rows_partition (s : ℕ) (xs : List RawVertex)
    (h : ∀ x∈xs,x.1<s+2) :
    ((xs.filter (fun x => x.1<s))++(xs.filter (fun x=>x.1=s))++
      (xs.filter (fun x=>x.1=s+1))).Perm xs := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht : ∀ y∈xs,y.1<s+2 := fun y hy => h y (by simp [hy])
    have H := ih ht
    by_cases ho : x.1<s
    · have h0 : x.1≠s := by omega
      have h1 : x.1≠s+1 := by omega
      simpa [ho,h0,h1] using H.cons x
    · by_cases h0 : x.1=s
      · have h1 : x.1≠s+1 := by omega
        simp [h0]
        simpa only [List.append_assoc,List.cons_append] using
          (List.perm_middle.append_right _).trans (H.cons x)
      · have h1 : x.1=s+1 := by omega
        simp [h1]
        simpa only [List.append_assoc] using List.perm_middle.trans (H.cons x)

/-- List lookup defaults are never used in the real pairing range. -/
theorem range_getD {α : Type*} (xs : List α) (d : α) :
    (List.range xs.length).map (fun i => xs.getD i d)=xs := by
  apply List.ext_getElem (by simp)
  intro i hi hj
  simp only [List.getElem_map,List.getElem_range]
  exact List.getD_eq_getElem xs d hj

theorem paired_endpoints (s : ℕ) (r : RawClosedNetwork) (hb : Balanced s r) :
    ((pairedRows s r).flatMap Prod.snd).Perm (pins s false r ++ pins s true r) := by
  have h := List.flatMap_append_perm (List.range (pins s false r).length)
    (fun i => [(pins s false r).getD i (0,false)])
    (fun i => [(pins s true r).getD i (0,false)])
  have hz : (List.range (pins s false r).length).flatMap
      (fun i => [(pins s false r).getD i (0,false)]) = pins s false r := by
    simpa only [←List.map_eq_flatMap] using range_getD (pins s false r) (0,false)
  have ho : (List.range (pins s false r).length).flatMap
      (fun i => [(pins s true r).getD i (0,false)]) = pins s true r := by
    rw [show (pins s false r).length=(pins s true r).length from hb]
    simpa only [←List.map_eq_flatMap] using range_getD (pins s true r) (0,false)
  rw [hz,ho] at h
  simpa [pairedRows,pairedRow,List.flatMap_map] using h.symm

theorem row_valid {s b : ℕ} {a : ℕ → ℕ} {r : RawClosedNetwork}
    (hr : r.WellFormed (s+2) b (sourceArity s a)) (row : RawVertex)
    (hm : row∈r.vertices) : row.1<s+2 ∧ row.2.length=sourceArity s a row.1 := by
  obtain ⟨v,rfl⟩ := List.mem_iff_get.mp hm
  exact hr.1 v

theorem pin_row_singleton {s b : ℕ} {a : ℕ → ℕ} {r : RawClosedNetwork}
    (hr : r.WellFormed (s+2) b (sourceArity s a)) (v : RawVertex)
    (hv : v∈r.vertices) (bit : Bool) (hl : v.1=s+bit.toNat) :
    ∃ p, v=(s+bit.toNat,[p]) := by
  have hlen := (row_valid hr v hv).2
  have hnot : ¬v.1<s := by cases bit <;> simp_all
  rw [sourceArity,if_neg hnot] at hlen
  obtain ⟨p,hp⟩ := List.length_eq_one_iff.mp hlen
  exact ⟨p,Prod.ext hl hp⟩

/-- Actual endpoint-list lengths equal the numbers of the corresponding
unary occurrences, because the original validator checks every singleton. -/
theorem pins_length_eq_count {s b : ℕ} {a : ℕ → ℕ} {r : RawClosedNetwork}
    (hr : r.WellFormed (s+2) b (sourceArity s a)) (bit : Bool) :
    (pins s bit r).length=(r.vertices.filter (fun row=>row.1=s+bit.toNat)).length := by
  have aux : ∀ xs : List RawVertex, (∀ row∈xs,row.2.length=1) →
      (xs.flatMap Prod.snd).length=xs.length := by
    intro xs hx
    induction xs with
    | nil => rfl
    | cons row rows ih =>
      have hrow := hx row (by simp)
      have htail := ih (fun row hm=>hx row (by simp [hm]))
      simp only [List.flatMap_cons,List.length_append,List.length_cons,hrow,htail]
      omega
  apply aux
  intro row hm
  obtain ⟨hv,hl⟩ := List.mem_filter.mp hm
  obtain ⟨p,rfl⟩ := pin_row_singleton hr row hv bit (of_decide_eq_true hl)
  rfl

theorem balanced_iff_pinCounts {s b : ℕ} {a : ℕ → ℕ} {r : RawClosedNetwork}
    (hr : r.WellFormed (s+2) b (sourceArity s a)) : Balanced s r ↔
    (r.vertices.filter (fun row=>row.1=s)).length=
      (r.vertices.filter (fun row=>row.1=s+1)).length := by
  unfold Balanced
  rw [pins_length_eq_count hr false,pins_length_eq_count hr true]
  rfl

/-- The entire endpoint multiset, including two distinct self-loop ends,
is preserved. Balance is proved by callers from actual occurrence counts. -/
theorem endpoints_perm {s b : ℕ} {a : ℕ → ℕ} {r : RawClosedNetwork}
    (hr : r.WellFormed (s+2) b (sourceArity s a)) (hb : Balanced s r) :
    (raw s r).endpoints.Perm r.endpoints := by
  have hp := (rows_partition s r.vertices (fun row hm => (row_valid hr row hm).1)).flatMap_right Prod.snd
  have hq := (paired_endpoints s r hb).append_left ((oldRows s r).flatMap Prod.snd)
  have hq' := hq.trans (by
    simpa [oldRows,pins,List.flatMap_append,List.append_assoc] using hp)
  simpa [RawClosedNetwork.endpoints,raw,←List.flatMap_def,List.flatMap_append] using hq'

/-- Valid original records and the actual balance identity suffice. There
is no supplied target validator or successful rewrite premise. -/
theorem wellFormed {s b : ℕ} {a : ℕ → ℕ} {r : RawClosedNetwork}
    (hr : r.WellFormed (s+2) b (sourceArity s a)) (hb : Balanced s r) :
    (raw s r).WellFormed (s+1) b (targetArity s a) := by
  refine ⟨?_,hr.2.1,?_⟩
  · intro v
    have hm := List.get_mem (raw s r).vertices v
    change (raw s r).vertices.get v∈oldRows s r++pairedRows s r at hm
    rcases List.mem_append.mp hm with ho|hp
    · obtain ⟨hmem,hlt⟩ := List.mem_filter.mp ho
      have hlt' : ((raw s r).vertices.get v).1<s := of_decide_eq_true hlt
      have hv := row_valid hr _ hmem
      refine ⟨by omega,hv.2.trans ?_⟩
      simp only [sourceArity,targetArity,if_pos hlt']
    · obtain ⟨i,hi,he⟩ := List.mem_map.mp hp
      rw [←he]
      exact ⟨by simp [pairedRow],by simp [pairedRow,targetArity]⟩
  · exact (endpoints_perm hr hb).trans hr.2.2

section Weighted
variable {K : Type*} [CommSemiring K]

/-- Total raw table; only the two distinguished legal labels use unaries. -/
def sourceTable (s : ℕ) (F : ℕ → List Bool → K) (P Q : Bool → K)
    (label : ℕ) (bits : List Bool) : K :=
  if label<s then F label bits else if label=s then P (bits.getD 0 false) else Q (bits.getD 0 false)

/-- The actual tensor product at two ordered ports. -/
def targetTable (s : ℕ) (F : ℕ → List Bool → K) (P Q : Bool → K)
    (label : ℕ) (bits : List Bool) : K :=
  if label<s then F label bits else P (bits.getD 0 false)*Q (bits.getD 1 false)

def rowWeight (F : ℕ → List Bool → K) (c : RawEndpoint → Bool) (row : RawVertex) : K :=
  F row.1 (row.2.map c)
def rowsWeight (F : ℕ → List Bool → K) (c : RawEndpoint → Bool) (rows : List RawVertex) : K :=
  (rows.map (rowWeight F c)).prod

theorem rowsWeight_append (F : ℕ → List Bool → K) (c : RawEndpoint → Bool)
    (xs ys : List RawVertex) : rowsWeight F c (xs++ys)=rowsWeight F c xs*rowsWeight F c ys := by
  simp [rowsWeight]

theorem singleton_rows_weight (F : ℕ → List Bool → K) (c : RawEndpoint → Bool)
    (label : ℕ) (P : Bool → K) (hspec : ∀ x,F label [x]=P x)
    (rows : List RawVertex) (hr : ∀ row∈rows,∃p,row=(label,[p])) :
    rowsWeight F c rows=((rows.flatMap Prod.snd).map (fun p=>P (c p))).prod := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    obtain ⟨p,rfl⟩ := hr row (by simp)
    have ht : ∀ row∈rows,∃p,row=(label,[p]) := fun row hm=>hr row (by simp [hm])
    simp only [rowsWeight,List.map_cons,List.prod_cons,rowWeight,List.map_nil,
      hspec,List.flatMap_cons,List.singleton_append,List.map_cons,List.prod_cons]
    exact congrArg (P (c p)*·) (ih ht)

theorem pin_rows_weight {s b : ℕ} {a : ℕ → ℕ} {r : RawClosedNetwork}
    (hr : r.WellFormed (s+2) b (sourceArity s a))
    (F : ℕ → List Bool → K) (P Q : Bool → K) (c : RawEndpoint → Bool) (bit : Bool) :
    rowsWeight (sourceTable s F P Q) c (r.vertices.filter (fun row=>row.1=s+bit.toNat))=
      ((pins s bit r).map (fun p=>if bit then Q (c p) else P (c p))).prod := by
  exact singleton_rows_weight (sourceTable s F P Q) c (s+bit.toNat)
    (fun x=>if bit then Q x else P x) (by
      intro x
      cases bit <;> simp [sourceTable]) _ (by
      intro row hm
      obtain ⟨hmem,he⟩ := List.mem_filter.mp hm
      exact pin_row_singleton hr row hmem bit (of_decide_eq_true he))
theorem paired_rows_weight (s : ℕ) (r : RawClosedNetwork) (hb : Balanced s r)
    (F : ℕ → List Bool → K) (P Q : Bool → K) (c : RawEndpoint → Bool) :
    rowsWeight (targetTable s F P Q) c (pairedRows s r)=
      ((pins s false r).map (fun p=>P (c p))).prod*
      ((pins s true r).map (fun p=>Q (c p))).prod := by
  have hz := congrArg (fun xs=>((xs : List RawEndpoint).map (fun p=>P (c p))).prod)
    (range_getD (pins s false r) (0,false))
  have ho := congrArg (fun xs=>((xs : List RawEndpoint).map (fun p=>Q (c p))).prod)
    (range_getD (pins s true r) (0,false))
  simp only [List.map_map,Function.comp_def] at hz ho
  simp only [rowsWeight,pairedRows,List.map_map,Function.comp_def,rowWeight,pairedRow,
    List.map_cons,List.map_nil,targetTable,Nat.lt_irrefl,ite_false,List.getD_cons_zero,
    List.getD_cons_succ]
  rw [List.prod_map_mul,hz]
  congr 1
  rw [show (pins s false r).length=(pins s true r).length from hb]
  exact ho

/-- Every full assignment keeps exactly the same weighted product. P and Q
may be arbitrary field/semiring weights, and all ordinary rows are untouched. -/
theorem assignment_weight {s b : ℕ} {a : ℕ → ℕ} {r : RawClosedNetwork}
    (hr : r.WellFormed (s+2) b (sourceArity s a)) (hb : Balanced s r)
    (F : ℕ → List Bool → K) (P Q : Bool → K) (c : RawEndpoint → Bool) :
    rowsWeight (targetTable s F P Q) c (raw s r).vertices=
      rowsWeight (sourceTable s F P Q) c r.vertices := by
  have hp := (rows_partition s r.vertices (fun row hm=>(row_valid hr row hm).1)).map
    (rowWeight (sourceTable s F P Q) c)
  have he := hp.prod_eq
  change rowsWeight (sourceTable s F P Q) c
    ((r.vertices.filter (fun row=>row.1<s))++(r.vertices.filter (fun row=>row.1=s))++
      (r.vertices.filter (fun row=>row.1=s+1))) = rowsWeight (sourceTable s F P Q) c r.vertices at he
  rw [←he]
  simp only [raw,rowsWeight_append]
  rw [paired_rows_weight s r hb]
  have ho : rowsWeight (targetTable s F P Q) c (oldRows s r)=
      rowsWeight (sourceTable s F P Q) c (oldRows s r) := by
    unfold rowsWeight
    congr 1
    apply List.map_congr_left
    intro row hrow
    have hlt : row.1<s := of_decide_eq_true (List.mem_filter.mp hrow).2
    simp only [rowWeight,targetTable,sourceTable,if_pos hlt]
  rw [ho]
  have hz := pin_rows_weight hr F P Q c false
  have ht := pin_rows_weight hr F P Q c true
  simp only [Bool.toNat_false,Nat.add_zero,Bool.toNat_true,Bool.false_eq_true,ite_false,ite_true] at hz ht
  rw [hz,ht]
  simp only [oldRows,mul_assoc]

end Weighted

section Signatures
variable {K : Type*} [CommSemiring K] {s : ℕ} {a : ℕ → ℕ}

/-- The old dictionary plus precisely the two supplied unary tables. -/
def sourceSignatures (G : (i : Fin s) → Signature K (a i.val)) (P Q : Bool → K)
    (i : Fin (s+2)) : Signature K (sourceArity s a i.val) := fun x =>
  if hi : i.val<s then
    G ⟨i.val,hi⟩ (fun j=>x ⟨j.val,by simpa [sourceArity,hi] using j.isLt⟩)
  else if i.val=s then P (x ⟨0,by simp [sourceArity,hi]⟩)
  else Q (x ⟨0,by simp [sourceArity,hi]⟩)

/-- The old dictionary plus the ordered product of the same unary tables. -/
def targetSignatures (G : (i : Fin s) → Signature K (a i.val)) (P Q : Bool → K)
    (i : Fin (s+1)) : Signature K (targetArity s a i.val) := fun x =>
  if hi : i.val<s then
    G ⟨i.val,hi⟩ (fun j=>x ⟨j.val,by simpa [targetArity,hi] using j.isLt⟩)
  else P (x ⟨0,by simp [targetArity,hi]⟩)*Q (x ⟨1,by simp [targetArity,hi]⟩)

/-- No normalization scalar is hidden in regrouping literal pins. -/
def pin (b x : Bool) : K := if x=b then 1 else 0

theorem paired_pin_table (u v : Bool) :
    pin (K:=K) false u*pin true v=(if u=false ∧ v=true then 1 else 0) := by
  cases u <;> cases v <;> simp [pin]

/-- The regrouped tensor is literally the oriented 01 matrix. -/
theorem target_pin_signature (G : (i : Fin s) → Signature K (a i.val))
    (x : Fin (targetArity s a s) → Bool) :
    targetSignatures G (pin false) (pin true) ⟨s,by omega⟩ x=
      if x ⟨0,by simp [targetArity]⟩=false ∧ x ⟨1,by simp [targetArity]⟩=true then 1 else 0 := by
  simpa [targetSignatures] using paired_pin_table (K:=K)
    (x ⟨0,by simp [targetArity]⟩) (x ⟨1,by simp [targetArity]⟩)

end Signatures

section Denotation
variable {K : Type*} [CommSemiring K]

/-- Finite signature-table extension. Out-of-range defaults are unreachable
on a validated input and do not change its actual network interpretation. -/
def rawTable {s : ℕ} {a : ℕ → ℕ} (G : (i : Fin s) → Signature K (a i.val))
    (label : ℕ) (bits : List Bool) : K :=
  if hi : label<s then G ⟨label,hi⟩ (fun i=>bits.getD i.val false) else 0

/-- The original addressed edge-end bit, extended only outside the validator. -/
def endpointBit (m : ℕ) (z : (Fin m × Bool) → Bool) (p : RawEndpoint) : Bool :=
  if hp : p.1<m then z (⟨p.1,hp⟩,p.2) else false

theorem assigned_port {s b : ℕ} {a : ℕ → ℕ} (r : RawClosedNetwork)
    (hr : r.WellFormed s b a) (z : (Fin r.edges.length × Bool) → Bool)
    (v : Fin r.vertices.length) (i : Fin (a (r.vertices.get v).1)) :
    (r.shape hr).assignment Fin.elim0 z v i=
      ((r.vertices.get v).2.map (endpointBit r.edges.length z)).getD i.val false := by
  have hi : i.val<(r.vertices.get v).2.length := by rw [(hr.1 v).2]; exact i.isLt
  rw [List.getD_eq_getElem _ _ (by simpa using hi),List.getElem_map]
  change z (r.route hr ⟨v,i⟩)=_
  have he := r.portEndpoint_bound hr ⟨v,i⟩
  simp only [RawClosedNetwork.portEndpoint,List.get_eq_getElem,Fin.val_cast] at he
  simp only [endpointBit,dif_pos he,RawClosedNetwork.route,RawClosedNetwork.portEndpoint,
    List.get_eq_getElem,Fin.val_cast]

/-- Exact full edge-end assignment expansion for arbitrary edge kernels.
Every vertex occurrence and every edge weight is retained. This is a semantic
finite sum, not an assertion that enumeration is a polynomial evaluator. -/
theorem denote_eq_rows_sum {s b : ℕ} {a : ℕ → ℕ} (r : RawClosedNetwork)
    (hr : r.WellFormed s b a) (G : (i : Fin s) → Signature K (a i.val))
    (E : Fin b → Bool → Bool → K) :
    (r.realize hr G E).denote Fin.elim0=
      ∑ z : (Fin r.edges.length × Bool) → Bool,
        rowsWeight (rawTable G) (endpointBit r.edges.length z) r.vertices*
          ∏ e : Fin r.edges.length,E (r.edgeLabel hr e) (z (e,false)) (z (e,true)) := by
  unfold Network.denote
  apply Finset.sum_congr rfl
  intro z _
  apply congrArg₂ (·*·) _ rfl
  rw [←List.prod_ofFn]
  unfold rowsWeight
  apply congrArg List.prod
  rw [←List.ofFn_getElem_eq_map r.vertices]
  apply congrArg List.ofFn
  funext v
  change G (r.signatureLabel hr v) ((r.shape hr).assignment Fin.elim0 z v)=
    rowWeight (rawTable G) (endpointBit r.edges.length z) (r.vertices.get v)
  unfold rowWeight rawTable
  rw [dif_pos (hr.1 v).1]
  congr 1
  funext i
  exact assigned_port r hr z v i

theorem source_table {s : ℕ} {a : ℕ → ℕ}
    (G : (i : Fin s) → Signature K (a i.val)) (P Q : Bool → K)
    (label : ℕ) (hl : label<s+2) (bits : List Bool) :
    rawTable (sourceSignatures G P Q) label bits=sourceTable s (rawTable G) P Q label bits := by
  by_cases hi : label<s
  · simp [rawTable,sourceSignatures,sourceTable,hl,hi]
  · simp [rawTable,sourceSignatures,sourceTable,hl,hi]

theorem target_table {s : ℕ} {a : ℕ → ℕ}
    (G : (i : Fin s) → Signature K (a i.val)) (P Q : Bool → K)
    (label : ℕ) (hl : label<s+1) (bits : List Bool) :
    rawTable (targetSignatures G P Q) label bits=targetTable s (rawTable G) P Q label bits := by
  by_cases hi : label<s
  · simp [rawTable,targetSignatures,targetTable,hl,hi]
  · simp [rawTable,targetSignatures,targetTable,hl,hi]

theorem source_weight {s b : ℕ} {a : ℕ → ℕ} {r : RawClosedNetwork}
    (hr : r.WellFormed (s+2) b (sourceArity s a))
    (G : (i : Fin s) → Signature K (a i.val)) (P Q : Bool → K) (c : RawEndpoint → Bool) :
    rowsWeight (rawTable (sourceSignatures G P Q)) c r.vertices=
      rowsWeight (sourceTable s (rawTable G) P Q) c r.vertices := by
  unfold rowsWeight
  congr 1
  apply List.map_congr_left
  intro row hm
  exact source_table G P Q row.1 (row_valid hr row hm).1 _

theorem target_weight {s b : ℕ} {a : ℕ → ℕ} {r : RawClosedNetwork}
    (hr : r.WellFormed (s+2) b (sourceArity s a)) (hb : Balanced s r)
    (G : (i : Fin s) → Signature K (a i.val)) (P Q : Bool → K) (c : RawEndpoint → Bool) :
    rowsWeight (rawTable (targetSignatures G P Q)) c (raw s r).vertices=
      rowsWeight (targetTable s (rawTable G) P Q) c (raw s r).vertices := by
  unfold rowsWeight
  congr 1
  apply List.map_congr_left
  intro row hm
  obtain ⟨v,rfl⟩ := List.mem_iff_get.mp hm
  exact target_table G P Q _ ((wellFormed hr hb).1 v).1 _

/-- The actual validated source and target networks have the same full
partition function for arbitrary old signatures, unary weights and edge
kernels. The algorithm supplies its own target validation; no denotation,
assignment pairing, realization or successful compiler is a caller premise. -/
theorem denote_preserved {s b : ℕ} {a : ℕ → ℕ} {r : RawClosedNetwork}
    (hr : r.WellFormed (s+2) b (sourceArity s a)) (hb : Balanced s r)
    (G : (i : Fin s) → Signature K (a i.val)) (P Q : Bool → K)
    (E : Fin b → Bool → Bool → K) :
    ((raw s r).realize (wellFormed hr hb) (targetSignatures G P Q) E).denote Fin.elim0=
      (r.realize hr (sourceSignatures G P Q) E).denote Fin.elim0 := by
  rw [denote_eq_rows_sum,denote_eq_rows_sum]
  apply Finset.sum_congr rfl
  intro z _
  rw [target_weight hr hb,source_weight hr]
  rw [assignment_weight hr hb]
  rfl

end Denotation

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.PairedPinsSemantics
