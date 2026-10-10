import Holant.Complexity.UniversalPairReduction.Smoothing
import Mathlib.Data.List.Nodup

/-! Exact endpoint accounting for deleting a complete native edge. The map is
bijective on all surviving endpoints, with no loop or simple-graph assumption. -/
namespace Holant.Complexity.UniversalPairReduction.Surgery
open FixedGadgetSubstitution Smoothing

 theorem ends_succ (m : ℕ) : edgeEnds 0 (m+1)=edgeEnds 0 m++[(m,false),(m,true)] := by
  rw [edgeEnds_add]
  simp [edgeEnds]

 theorem ends_nodup (m : ℕ) : (edgeEnds 0 m).Nodup := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [ends_succ,List.nodup_append]
    refine ⟨ih,by simp,?_⟩
    intro p hp q hq he
    subst q
    have hb := (Template.mem_edgeEnds 0 m p).mp hp
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at hq
    rcases hq with rfl|rfl <;> omega

 theorem ends_mem (m : ℕ) (p : RawEndpoint) : p∈edgeEnds 0 m ↔ p.1<m := by
  simpa using Template.mem_edgeEnds 0 m p

def liftEdge (removed edge : ℕ) : ℕ := if edge<removed then edge else edge+1

 theorem lower_injective {e a b : ℕ} (ha : a≠e) (hb : b≠e)
    (h : lowerEdge e a=lowerEdge e b) : a=b := by
  unfold lowerEdge at h
  split_ifs at h <;> omega

 theorem lower_lt {m e a : ℕ} (he : e<m) (ha : a<m) (hne : a≠e) : lowerEdge e a<m-1 := by
  unfold lowerEdge
  split_ifs <;> omega

 theorem lift_lt {m e a : ℕ} (he : e<m) (ha : a<m-1) : liftEdge e a<m := by
  unfold liftEdge
  split_ifs <;> omega

 theorem lift_ne (e a : ℕ) : liftEdge e a≠e := by
  unfold liftEdge
  split_ifs <;> omega

 theorem lower_lift (e a : ℕ) : lowerEdge e (liftEdge e a)=a := by
  unfold liftEdge lowerEdge
  split_ifs <;> omega

 theorem lift_lower {e a : ℕ} (ha : a≠e) : liftEdge e (lowerEdge e a)=a := by
  unfold liftEdge lowerEdge
  split_ifs <;> omega

 theorem lower_endpoint_injective {e : ℕ} {p q : RawEndpoint}
    (hp : p.1≠e) (hq : q.1≠e)
    (he : removeLoopEndpoint e p=removeLoopEndpoint e q) : p=q := by
  apply Prod.ext
  · exact lower_injective hp hq (congrArg Prod.fst he)
  · simpa only [removeLoopEndpoint] using congrArg Prod.snd he

/-- A list containing each surviving old endpoint exactly once emits exactly
the canonical endpoints of the one-edge-shorter record. -/
theorem lower_partition (m e : ℕ) (he : e<m) (L : List RawEndpoint)
    (hn : L.Nodup) (hm : ∀p,p∈L ↔ p.1<m ∧ p.1≠e) :
    (L.map (removeLoopEndpoint e)).Perm (edgeEnds 0 (m-1)) := by
  apply (List.perm_ext_iff_of_nodup
    (List.Nodup.map_on (fun p hp q hq h =>
      lower_endpoint_injective (hm p |>.mp hp).2 (hm q |>.mp hq).2 h) hn)
    (ends_nodup _)).mpr
  intro p
  rw [List.mem_map,ends_mem]
  constructor
  · rintro ⟨q,hq,rfl⟩
    exact lower_lt he (hm q |>.mp hq).1 (hm q |>.mp hq).2
  · intro hp
    refine ⟨(liftEdge e p.1,p.2),(hm _).mpr ⟨lift_lt he hp,lift_ne _ _⟩,?_⟩
    simp [removeLoopEndpoint,lower_lift]

/-- Removing both endpoints of the same edge leaves exactly its complement. -/
theorem loop_remainder (m e : ℕ) (bit : Bool) (L : List RawEndpoint)
    (hp : ((e,bit)::(e,!bit)::L).Perm (edgeEnds 0 m)) :
    L.Nodup ∧ ∀p,p∈L ↔ p.1<m ∧ p.1≠e := by
  have hn := hp.symm.nodup (ends_nodup m)
  simp only [List.nodup_cons] at hn
  refine ⟨hn.2.2,?_⟩
  intro p
  constructor
  · intro hL
    have hb := (ends_mem m p).mp (hp.mem_iff.mp (by simp [hL]))
    refine ⟨hb,?_⟩
    intro he
    rcases p with ⟨j,b⟩
    dsimp at he
    subst j
    cases bit <;> cases b <;> simp_all
  · rintro ⟨hb,hne⟩
    have hL := hp.mem_iff.mpr ((ends_mem m p).mpr hb)
    simp only [List.mem_cons] at hL
    rcases hL with hL|hL|hL
    · exact (hne (congrArg Prod.fst hL)).elim
    · exact (hne (congrArg Prod.fst hL)).elim
    · exact hL

 theorem loop_partition (m e : ℕ) (he : e<m) (bit : Bool) (L : List RawEndpoint)
    (hp : ((e,bit)::(e,!bit)::L).Perm (edgeEnds 0 m)) :
    (L.map (removeLoopEndpoint e)).Perm (edgeEnds 0 (m-1)) :=
  lower_partition m e he L (loop_remainder m e bit L hp).1
    (loop_remainder m e bit L hp).2

end Holant.Complexity.UniversalPairReduction.Surgery
