import Holant.ReedMuller.WeightTwoIntegration.CrossCards

/-! Perfection of the original nonempty weight-two matching, derived from
actual cross-card matchings. No parity count or perfect support is assumed. -/
noncomputable section
namespace Holant.ReedMuller.WeightTwoIntegration
open Holant.ReedMuller.ZeroCardGraph Holant.ReedMuller.MatchingConsistency
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

 private theorem outside_small (s : Finset ι) (h : s.card<Fintype.card ι) : ∃k,k∉s := by
  obtain ⟨k,_,hk⟩ := Finset.exists_mem_notMem_of_card_lt_card (by simpa using h : s.card<Finset.univ.card)
  exact ⟨k,hk⟩

 theorem cross_matching_disjoint_edge (W : SimpleGraph ι) (hn : 6≤Fintype.card ι)
    (u v : ι) (huv : W.Adj u v)
    (hcross : ∀k,u≠k → v≠k → Nonempty (CrossMatching W u v k)) :
    ∃a b,W.Adj a b ∧ a≠u ∧ a≠v ∧ b≠u ∧ b≠v := by
  obtain ⟨k,hk⟩ := outside_small ({u,v} : Finset ι) (by
    have hs : ({u,v} : Finset ι).card≤2 := Finset.card_le_two
    omega)
  have hku : k≠u := by simpa using (fun hh => hk (by simp [hh]) : k≠u)
  have hkv : k≠v := by intro hh; exact hk (by simp [hh])
  obtain ⟨C⟩ := hcross k hku.symm hkv.symm
  let v' : Remaining u k := ⟨v,huv.ne.symm,hkv.symm⟩
  have hrem := remaining_card_add_two u k hku.symm
  obtain ⟨p,hp⟩ := outside_small ({v',C.pairing.mate v'} : Finset (Remaining u k)) (by
    have hs : ({v',C.pairing.mate v'} : Finset (Remaining u k)).card≤2 := Finset.card_le_two
    omega)
  have hpv : p≠v' := by intro h; exact hp (by simp [h])
  have hpm : p≠C.pairing.mate v' := by intro h; exact hp (by simp [h])
  have hqv : C.pairing.mate p≠v' := by
    intro h
    exact hpm ((C.pairing.mate_eq_iff p v').mp h).symm
  refine ⟨p.val,(C.pairing.mate p).val,?_,p.property.1,?_,(C.pairing.mate p).property.1,?_⟩
  · exact (C.internal p (C.pairing.mate p)
      (fun h => hpv (Subtype.ext h)) (fun h => hqv (Subtype.ext h))).mp rfl
  · exact fun h => hpv (Subtype.ext h)
  · exact fun h => hqv (Subtype.ext h)

 theorem perfect_of_cross_matchings (W : SimpleGraph ι) (hn : 6≤Fintype.card ι)
    (hmatch : ∀u v w,W.Adj u v → W.Adj u w → v=w)
    (u v : ι) (huv : W.Adj u v)
    (hcross : ∀k,u≠k → v≠k → Nonempty (CrossMatching W u v k)) :
    ∀x,∃y,W.Adj x y := by
  obtain ⟨a,b,hab,hau,hav,hbu,hbv⟩ := cross_matching_disjoint_edge W hn u v huv hcross
  obtain ⟨C⟩ := hcross a hau.symm hav.symm
  let v' : Remaining u a := ⟨v,huv.ne.symm,hav.symm⟩
  let b' : Remaining u a := ⟨b,hbu,hab.ne.symm⟩
  have hbmate : C.pairing.mate b'=v' := by
    apply Subtype.ext
    by_contra h
    have he := (C.internal b' (C.pairing.mate b') hbv h).mp rfl
    have heq := hmatch b a (C.pairing.mate b').val hab.symm he
    exact (C.pairing.mate b').property.2 heq.symm
  intro x
  by_cases hxu : x=u
  · subst x; exact ⟨v,huv⟩
  by_cases hxv : x=v
  · subst x; exact ⟨u,huv.symm⟩
  by_cases hxa : x=a
  · subst x; exact ⟨b,hab⟩
  by_cases hxb : x=b
  · subst x; exact ⟨a,hab.symm⟩
  let x' : Remaining u a := ⟨x,hxu,hxa⟩
  have hmate : (C.pairing.mate x').val≠v := by
    intro h
    have he : C.pairing.mate x'=v' := Subtype.ext h
    have heq := C.pairing.injective (he.trans hbmate.symm)
    exact hxb (congrArg Subtype.val heq)
  exact ⟨(C.pairing.mate x').val,(C.internal x' (C.pairing.mate x') hxv hmate).mp rfl⟩

 theorem weight_graph_perfect {K : Type*} [Field K] (htwo : (2:K)≠0)
    {f : Holant.Tensor K ι} (H : Consistent f) (hd : EqualityDeck f)
    (hn : 6≤Fintype.card ι) (u v : ι) (huv : (weightGraph f).Adj u v) :
    ∀x,∃y,(weightGraph f).Adj x y :=
  perfect_of_cross_matchings (weightGraph f) hn H.weight_matching u v huv
    (fun k huk hvk => actual_cross_matching htwo H hd u v k huv huk hvk)

end Holant.ReedMuller.WeightTwoIntegration
