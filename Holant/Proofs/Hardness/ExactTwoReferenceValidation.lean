import Holant.Proofs.Hardness.ExactTwoReferenceRaw
import Holant.Complexity.FixedGadgetSubstitution.WellFormed
import Mathlib.Data.List.FinRange

/-! The shared-reference cycle is validated from original
rows alone. The cyclic predecessor permutes actual new edge IDs; the argument
retains endpoint multiplicities, loops, parallel edges and all ordered old ports. -/
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.ExactTwoReferenceValidation
open Holant.Complexity FixedGadgetSubstitution ExactTwoReferenceRaw
set_option backward.isDefEq.respectTransparency false

 theorem previous_lt {m i : ℕ} (hi : i<m) : previous m i<m := by
  unfold previous
  split_ifs <;> omega

def previousFin {m : ℕ} (i : Fin m) : Fin m := ⟨previous m i.val,previous_lt i.isLt⟩
def nextFin {m : ℕ} (i : Fin m) : Fin m :=
  ⟨if i.val+1<m then i.val+1 else 0,by split_ifs <;> omega⟩

theorem next_previous {m : ℕ} (i : Fin m) : nextFin (previousFin i)=i := by
  apply Fin.ext
  have hi := i.isLt
  simp only [nextFin,previousFin,previous]
  split_ifs <;> omega

theorem previous_next {m : ℕ} (i : Fin m) : previousFin (nextFin i)=i := by
  apply Fin.ext
  have hi := i.isLt
  change previous m (if i.val+1<m then i.val+1 else 0)=i.val
  by_cases h : i.val+1<m
  · simp [h,previous]
  · simp only [if_neg h,previous,ite_true]
    omega

def previousPerm (m : ℕ) : Equiv.Perm (Fin m) where
  toFun := previousFin
  invFun := nextFin
  left_inv := next_previous
  right_inv := previous_next

 theorem range_map_ofFn {α : Type*} (m : ℕ) (f : ℕ → α) :
    (List.range m).map f=List.ofFn (fun i : Fin m=>f i.val) := by
  apply List.ext_getElem <;> simp

 theorem source_row {r : RawClosedNetwork} (hr : r.WellFormed 2 1 sourceArity)
    (v : RawVertex) (hv : v∈r.vertices) : v.1<2 ∧ v.2.length=sourceArity v.1 := by
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hv
  exact hr.1 i

 theorem rows_partition {r : RawClosedNetwork} (hr : r.WellFormed 2 1 sourceArity) :
    (oldRows r++pinRows r).Perm r.vertices := by
  have aux (xs : List RawVertex) (h : ∀v∈xs,v.1<2) :
      (xs.filter (fun v=>v.1<1)++xs.filter (fun v=>v.1==1)).Perm xs := by
    induction xs with
    | nil => simp
    | cons v vs ih =>
        have hv := h v (by simp)
        have H := ih (fun w hw=>h w (by simp [hw]))
        by_cases h0 : v.1<1
        · have h1 : v.1≠1 := by omega
          have hz : v.1=0 := by omega
          simpa [hz] using H.cons v
        · have h1 : v.1=1 := by omega
          simpa [h1] using List.perm_middle.trans (H.cons v)
  exact aux r.vertices (fun v hv=>(source_row hr v hv).1)

 theorem pin_ports {r : RawClosedNetwork} (hr : r.WellFormed 2 1 sourceArity)
    (i : ℕ) (hi : i<count r) :
    ((pinRows r).getD i (0,[])).2=
      [((pinRows r).getD i (0,[])).2.getD 0 (0,false),
       ((pinRows r).getD i (0,[])).2.getD 1 (0,false)] := by
  have hmem : (pinRows r).getD i (0,[])∈pinRows r := by
    rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem hi
  obtain ⟨hv,hl⟩ := List.mem_filter.mp hmem
  have hl' : ((pinRows r).getD i (0,[])).1=1 := by simpa using hl
  have hh := (source_row hr _ hv).2
  have hlen : ((pinRows r).getD i (0,[])).2.length=2 := by
    rw [hl'] at hh
    exact hh
  obtain ⟨p,q,hpq⟩ := List.length_eq_two.mp hlen
  rw [hpq]
  rfl

 theorem row_ports {r : RawClosedNetwork} (hr : r.WellFormed 2 1 sourceArity)
    (i : ℕ) (hi : i<count r) :
    (row r i).2=((pinRows r).getD i (0,[])).2++
      [(r.edges.length+previous (count r) i,true),(r.edges.length+i,false)] := by
  rw [pin_ports hr i hi]
  rfl

def freshEndpoints (offset m : ℕ) : List RawEndpoint :=
  (List.range m).flatMap fun i=>[(offset+previous m i,true),(offset+i,false)]

 theorem freshEndpoints_perm (offset m : ℕ) :
    (freshEndpoints offset m).Perm (edgeEnds offset m) := by
  have hp : ((List.range m).map (fun i=>(offset+previous m i,true))).Perm
      ((List.range m).map (fun i=>(offset+i,true))) := by
    rw [range_map_ofFn,range_map_ofFn]
    exact (previousPerm m).ofFn_comp_perm (fun i=>(offset+i.val,true))
  have hfirst := (List.flatMap_append_perm (List.range m)
    (fun i=>[(offset+previous m i,true)]) (fun i=>[(offset+i,false)])).symm
  have hlast := List.flatMap_append_perm (List.range m)
    (fun i=>[(offset+i,false)]) (fun i=>[(offset+i,true)])
  have hf : (freshEndpoints offset m).Perm
      ((List.range m).map (fun i=>(offset+previous m i,true))++
        (List.range m).map (fun i=>(offset+i,false))) := by
    simpa only [freshEndpoints,List.singleton_append,←List.map_eq_flatMap] using hfirst
  have hl : ((List.range m).map (fun i=>(offset+i,false))++
      (List.range m).map (fun i=>(offset+i,true))).Perm (edgeEnds offset m) := by
    simpa only [edgeEnds,List.singleton_append,←List.map_eq_flatMap] using hlast
  exact hf.trans ((hp.append_right _).trans (List.perm_append_comm.trans hl))

 theorem rows_endpoints {r : RawClosedNetwork} (hr : r.WellFormed 2 1 sourceArity) :
    ((rows r).flatMap Prod.snd).Perm ((pinRows r).flatMap Prod.snd++freshEndpoints r.edges.length (count r)) := by
  have he : (rows r).flatMap Prod.snd=(List.range (count r)).flatMap
      (fun i=>((pinRows r).getD i (0,[])).2++
        [(r.edges.length+previous (count r) i,true),(r.edges.length+i,false)]) := by
    simp only [rows,List.flatMap_map]
    apply List.flatMap_congr
    intro i hi
    exact row_ports hr i (List.mem_range.mp hi)
  rw [he]
  have hp := (List.flatMap_append_perm (List.range (count r))
    (fun i=>((pinRows r).getD i (0,[])).2)
    (fun i=>[(r.edges.length+previous (count r) i,true),(r.edges.length+i,false)])).symm
  have hold : (List.range (count r)).flatMap (fun i=>((pinRows r).getD i (0,[])).2)=
      (pinRows r).flatMap Prod.snd := by
    rw [←List.flatMap_map,show count r=(pinRows r).length from rfl,map_range_getD]
  rw [hold] at hp
  exact hp

 theorem endpoints_perm {r : RawClosedNetwork} (hr : r.WellFormed 2 1 sourceArity) :
    (raw r).endpoints.Perm (r.endpoints++edgeEnds r.edges.length (count r)) := by
  have hp := (rows_partition hr).flatMap_right Prod.snd
  have hq := (rows_endpoints hr).append_left ((oldRows r).flatMap Prod.snd)
  have hz := hq.trans (by
    simpa only [List.flatMap_append,List.append_assoc] using
      hp.append_right (freshEndpoints r.edges.length (count r)))
  have hfinal := hz.trans ((freshEndpoints_perm r.edges.length (count r)).append_left
    (r.vertices.flatMap Prod.snd))
  simpa only [RawClosedNetwork.endpoints,raw,←List.flatMap_def,List.flatMap_append] using hfinal

 theorem wellFormed {r : RawClosedNetwork} (hr : r.WellFormed 2 1 sourceArity) :
    (raw r).WellFormed 2 1 targetArity := by
  refine ⟨?_,?_,?_⟩
  · intro i
    have hi := List.get_mem (raw r).vertices i
    change (raw r).vertices.get i∈oldRows r++rows r at hi
    rcases List.mem_append.mp hi with ho|hn
    · obtain ⟨hv,hl⟩ := List.mem_filter.mp ho
      have hl' : ((raw r).vertices.get i).1<1 := of_decide_eq_true hl
      have hv' := source_row hr _ hv
      refine ⟨by omega,?_⟩
      simpa only [sourceArity,PairedPinsRaw.targetArity,if_pos hl',targetArity] using hv'.2
    · obtain ⟨j,hj,he⟩ := List.mem_map.mp hn
      rw [←he]
      exact ⟨by simp [row],row_arity r j⟩
  · intro i
    have hi := List.get_mem (raw r).edges i
    rcases List.mem_append.mp hi with ho|hn
    · obtain ⟨j,hj⟩ := List.mem_iff_get.mp ho
      rw [←hj]
      exact hr.2.1 j
    · have hz := (List.mem_replicate.mp hn).2
      rw [hz]
      decide
  · have h := (endpoints_perm hr).trans (hr.2.2.append_right (edgeEnds r.edges.length (count r)))
    rw [expectedEndpoints_eq] at h ⊢
    rw [edges_length,edgeEnds_add]
    simpa only [Nat.zero_add] using h

 theorem zero_raw {r : RawClosedNetwork} (hr : r.WellFormed 2 1 sourceArity)
    (hz : count r=0) : raw r=r := by
  have hp : pinRows r=[] := List.eq_nil_of_length_eq_zero hz
  have ho : oldRows r=r.vertices := by
    apply List.filter_eq_self.mpr
    intro v hv
    have hb := (source_row hr v hv).1
    have hn : v.1≠1 := by
      intro h
      have hm : v∈pinRows r := List.mem_filter.mpr ⟨hv,by simp [h]⟩
      simpa [hp] using hm
    have hl : v.1<1 := by omega
    simpa using hl
  simp [raw,rows,hz,ho]

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.ExactTwoReferenceValidation
