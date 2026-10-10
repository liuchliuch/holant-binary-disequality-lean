import Holant.Proofs.Hardness.GeneralEOSinglePinAmplificationRaw

/-! Original ordered incidences validate the anchored DEQ4 graph. The output
has exactly one literal pin for every source, including a source with none. -/
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOSinglePinAmplificationValidation
open Holant.Complexity FixedGadgetSubstitution UniversalPairReduction
open GeneralEOSinglePinAmplificationRaw
open ExactTwoReferenceValidation (range_map_ofFn freshEndpoints freshEndpoints_perm)
set_option backward.isDefEq.respectTransparency false
variable {s j : ℕ} {a : ℕ → ℕ}
 theorem source_row {r : RawClosedNetwork} (hr : r.WellFormed (s+1) 1 (extendedArity s a))
    (v : RawVertex) (hv : v∈r.vertices) : v.1<s+1 ∧ v.2.length=extendedArity s a v.1 := by
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hv
  exact hr.1 i

 theorem rows_partition {r : RawClosedNetwork} (hr : r.WellFormed (s+1) 1 (extendedArity s a)) :
    (oldRows s r++pinRows s r).Perm r.vertices := by
  have aux (xs : List RawVertex) (h : ∀v∈xs,v.1<s+1) :
      (xs.filter (fun v=>v.1<s)++xs.filter (fun v=>v.1==s)).Perm xs := by
    induction xs with
    | nil => simp
    | cons v vs ih =>
        have hv := h v (by simp)
        have H := ih (fun w hw=>h w (by simp [hw]))
        by_cases h0 : v.1<s
        · have h1 : v.1≠s := by omega
          simpa [h0,h1] using H.cons v
        · have h1 : v.1=s := by omega
          simpa [h1] using List.perm_middle.trans (H.cons v)
  exact aux r.vertices (fun v hv=>(source_row hr v hv).1)

 theorem pin_ports {r : RawClosedNetwork} (hr : r.WellFormed (s+1) 1 (extendedArity s a))
    (i : ℕ) (hi : i<count s r) :
    ((pinRows s r).getD i (0,[])).2=
      [((pinRows s r).getD i (0,[])).2.getD 0 (0,false),
       ((pinRows s r).getD i (0,[])).2.getD 1 (0,false)] := by
  have hmem : (pinRows s r).getD i (0,[])∈pinRows s r := by
    rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem hi
  obtain ⟨hv,hl⟩ := List.mem_filter.mp hmem
  have hl' : ((pinRows s r).getD i (0,[])).1=s := by simpa using hl
  have hh := (source_row hr _ hv).2
  have hlen : ((pinRows s r).getD i (0,[])).2.length=2 := by
    rw [hl'] at hh
    simpa [extendedArity] using hh
  obtain ⟨p,q,hpq⟩ := List.length_eq_two.mp hlen
  rw [hpq]
  rfl

 theorem row_ports {r : RawClosedNetwork} (hr : r.WellFormed (s+1) 1 (extendedArity s a))
    (i : ℕ) (hi : i<count s r) :
    (row s j r i).2=((pinRows s r).getD i (0,[])).2++
      reference s r (i+1) := by
  rw [pin_ports hr i hi]
  rfl


theorem fresh_decompose (s : ℕ) (r : RawClosedNetwork) :
    reference s r 0++(List.range (count s r)).flatMap (fun i => reference s r (i+1))=
      freshEndpoints r.edges.length (count s r+1) := by
  rw [freshEndpoints,List.range_succ_eq_map,List.flatMap_cons,List.flatMap_map]
  rfl

theorem rows_endpoints {r : RawClosedNetwork} (hr : r.WellFormed (s+1) 1 (extendedArity s a)) :
    ((rows s j r).flatMap Prod.snd).Perm ((pinRows s r).flatMap Prod.snd++
      (List.range (count s r)).flatMap (fun i => reference s r (i+1))) := by
  have he : (rows s j r).flatMap Prod.snd=(List.range (count s r)).flatMap
      (fun i => ((pinRows s r).getD i (0,[])).2++reference s r (i+1)) := by
    simp only [rows,List.flatMap_map]
    apply List.flatMap_congr
    intro i hi
    exact row_ports hr i (List.mem_range.mp hi)
  rw [he]
  have hp := (List.flatMap_append_perm (List.range (count s r))
    (fun i => ((pinRows s r).getD i (0,[])).2) (fun i => reference s r (i+1))).symm
  have hold : (List.range (count s r)).flatMap (fun i => ((pinRows s r).getD i (0,[])).2)=
      (pinRows s r).flatMap Prod.snd := by
    rw [←List.flatMap_map,show count s r=(pinRows s r).length from rfl,map_range_getD]
  rw [hold] at hp
  exact hp

theorem endpoints_perm {r : RawClosedNetwork} (hr : r.WellFormed (s+1) 1 (extendedArity s a)) :
    (raw s j r).endpoints.Perm (r.endpoints++edgeEnds r.edges.length (count s r+1)) := by
  have hrows := (rows_endpoints (j:=j) hr).append_left (reference s r 0)
  have hreorder : (reference s r 0++((pinRows s r).flatMap Prod.snd++
      (List.range (count s r)).flatMap (fun i => reference s r (i+1)))).Perm
      ((pinRows s r).flatMap Prod.snd++freshEndpoints r.edges.length (count s r+1)) := by
    rw [←fresh_decompose]
    simpa only [List.append_assoc] using
      (List.perm_append_comm (l₁:=reference s r 0) (l₂:=(pinRows s r).flatMap Prod.snd)).append_right
        ((List.range (count s r)).flatMap (fun i => reference s r (i+1)))
  have h := (hrows.trans hreorder).append_left ((oldRows s r).flatMap Prod.snd)
  have hpart := (rows_partition hr).flatMap_right Prod.snd
  have h' := h.trans (by
    simpa only [List.flatMap_append,List.append_assoc] using
      hpart.append_right (freshEndpoints r.edges.length (count s r+1)))
  have hfinal := h'.trans ((freshEndpoints_perm r.edges.length (count s r+1)).append_left
    (r.vertices.flatMap Prod.snd))
  simpa only [RawClosedNetwork.endpoints,raw,anchor,List.flatMap_cons,
    ←List.flatMap_def,List.flatMap_append,List.append_assoc] using hfinal

theorem wellFormed {r : RawClosedNetwork} (hr : r.WellFormed (s+1) 1 (extendedArity s a))
    (hj : j<s) (ha : a j=4) : (raw s j r).WellFormed (s+1) 1 (extendedArity s a) := by
  refine ⟨?_,?_,?_⟩
  · intro i
    have hi := List.get_mem (raw s j r).vertices i
    change (raw s j r).vertices.get i∈oldRows s r++anchor s r::rows s j r at hi
    rcases List.mem_append.mp hi with ho|hn
    · obtain ⟨hv,hl⟩ := List.mem_filter.mp ho
      exact source_row hr _ hv
    · rcases List.mem_cons.mp hn with he|he
      · rw [he]
        exact ⟨Nat.lt_succ_self s,by simp [anchor,reference,extendedArity]⟩
      · obtain ⟨k,hk,he⟩ := List.mem_map.mp he
        rw [←he]
        exact ⟨by simpa only [row_label] using Nat.lt_trans hj (Nat.lt_succ_self s),
          by simp [row_arity,row_label,extendedArity,hj,ha]⟩
  · intro i
    have hi := List.get_mem (raw s j r).edges i
    rcases List.mem_append.mp hi with ho|hn
    · obtain ⟨k,hk⟩ := List.mem_iff_get.mp ho
      rw [←hk]
      exact hr.2.1 k
    · rw [(List.mem_replicate.mp hn).2]
      decide
  · have h := (endpoints_perm (j:=j) hr).trans
      (hr.2.2.append_right (edgeEnds r.edges.length (count s r+1)))
    rw [expectedEndpoints_eq] at h ⊢
    rw [edges_length,show r.edges.length+count s r+1=r.edges.length+(count s r+1) by omega,edgeEnds_add]
    simpa only [Nat.zero_add] using h

theorem pin_count (r : RawClosedNetwork) (hj : j<s) : occurrences s (raw s j r)=1 := by
  have ho : ((oldRows s r).filter (fun v => v.1==s))=[] := by
    apply List.filter_eq_nil_iff.mpr
    intro v hv
    have hl : v.1<s := of_decide_eq_true (List.mem_filter.mp hv).2
    simp [show v.1≠s by omega]
  have hn : ((rows s j r).filter (fun v => v.1==s))=[] := by
    apply List.filter_eq_nil_iff.mpr
    intro v hv
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hv
    simp [row_label,show j≠s by omega]
  simp [occurrences,raw,List.filter_append,ho,hn,anchor]

theorem vertex_count {r : RawClosedNetwork} (hr : r.WellFormed (s+1) 1 (extendedArity s a)) :
    (raw s j r).vertices.length=r.vertices.length+1 := by
  have h := (rows_partition hr).length_eq
  simpa only [List.length_append,count,vertices_length] using congrArg (fun n => n+1) h

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOSinglePinAmplificationValidation
