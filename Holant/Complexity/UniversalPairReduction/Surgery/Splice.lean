import Holant.Complexity.UniversalPairReduction.Surgery.Endpoints

/-! Two-edge native-X surgery is endpoint transposition followed by deletion of
one complete edge. This preserves endpoint multiplicity, including parallel
attachments whose surviving ends belong to the same vertex. -/
namespace Holant.Complexity.UniversalPairReduction.Surgery
open FixedGadgetSubstitution Smoothing

 theorem swap_bound (m : ℕ) (p q : RawEndpoint) (hp : p.1<m) (hq : q.1<m)
    (r : RawEndpoint) : ((Equiv.swap p q) r).1<m ↔ r.1<m := by
  by_cases hrp : r=p
  · subst r
    simp [hp,hq]
  · by_cases hrq : r=q
    · subst r
      simp [hp,hq]
    · rw [Equiv.swap_apply_of_ne_of_ne hrp hrq]

 theorem swap_partition (m : ℕ) (p q : RawEndpoint) (hp : p.1<m) (hq : q.1<m) :
    ((edgeEnds 0 m).map (Equiv.swap p q)).Perm (edgeEnds 0 m) := by
  apply (List.perm_ext_iff_of_nodup ((ends_nodup m).map (Equiv.swap p q).injective)
    (ends_nodup m)).mpr
  intro r
  rw [List.mem_map,ends_mem]
  constructor
  · rintro ⟨t,ht,rfl⟩
    exact (swap_bound m p q hp hq t).mpr ((ends_mem m t).mp ht)
  · intro hr
    refine ⟨Equiv.swap p q r,(ends_mem m _).mpr ((swap_bound m p q hp hq r).mpr hr),?_⟩
    simp

 theorem remainder_ne (m : ℕ) (p q : RawEndpoint) (L : List RawEndpoint)
    (hp : (p::q::L).Perm (edgeEnds 0 m)) (r : RawEndpoint) (hr : r∈L) : r≠p ∧ r≠q := by
  have hn := hp.symm.nodup (ends_nodup m)
  simp only [List.nodup_cons] at hn
  constructor
  · intro he
    subst r
    exact hn.1 (by simp [hr])
  · intro he
    subst r
    exact hn.2.1 hr

/-- On every surviving endpoint, the raw splice map is exactly this
transposition-and-lowering map. -/
theorem splice_eq_swap (p q r : RawEndpoint) (hne : p.1≠q.1)
    (hrp : r≠p) (hrq : r≠q) :
    spliceEndpoint p q r = removeLoopEndpoint q.1 ((Equiv.swap p (q.1,!q.2)) r) := by
  by_cases he : r.1=q.1
  · have hr : r=(q.1,!q.2) := by
      apply Prod.ext
      · exact he
      · rcases r with ⟨e,b⟩
        rcases q with ⟨f,c⟩
        dsimp at he ⊢
        subst e
        cases b <;> cases c <;> simp_all
    subst r
    simp [spliceEndpoint,removeLoopEndpoint]
  · have hrn : r≠(q.1,!q.2) := by
      intro hx
      have hx1 := congrArg (fun t : RawEndpoint => t.1) hx
      exact he hx1
    rw [Equiv.swap_apply_of_ne_of_ne hrp hrn]
    simp [spliceEndpoint,removeLoopEndpoint,he]

 theorem splice_partition (m : ℕ) (p q : RawEndpoint) (L : List RawEndpoint)
    (hne : p.1≠q.1) (hp : (p::q::L).Perm (edgeEnds 0 m)) :
    (L.map (spliceEndpoint p q)).Perm (edgeEnds 0 (m-1)) := by
  have hpbound : p.1<m := (ends_mem m p).mp (hp.mem_iff.mp (by simp))
  have hqbound : q.1<m := (ends_mem m q).mp (hp.mem_iff.mp (by simp))
  have hqp : q≠p := by intro he; exact hne (congrArg Prod.fst he).symm
  have hqm : q≠(q.1,!q.2) := by
    intro he
    have hb := congrArg Prod.snd he
    generalize q.2=b at hb
    cases b <;> cases hb
  have hh := (hp.map (Equiv.swap p (q.1,!q.2))).trans
    (swap_partition m p (q.1,!q.2) hpbound hqbound)
  simp only [List.map_cons,Equiv.swap_apply_left,
    Equiv.swap_apply_of_ne_of_ne hqp hqm] at hh
  have hc := loop_partition m q.1 hqbound (!q.2) (L.map (Equiv.swap p (q.1,!q.2)))
    (by simpa only [Bool.not_not] using hh)
  rw [List.map_map] at hc
  convert hc using 1
  apply List.map_congr_left
  intro r hr
  exact splice_eq_swap p q r hne (remainder_ne m p q L hp r hr).1
    (remainder_ne m p q L hp r hr).2

end Holant.Complexity.UniversalPairReduction.Surgery
