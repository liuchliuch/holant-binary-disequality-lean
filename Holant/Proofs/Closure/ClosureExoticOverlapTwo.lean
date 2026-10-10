import Holant.Pauli.ExoticKlein.MatchingFour

/-! Exact two-coordinate variation of a four-term matching overlap. The
coefficient support is the literal full matching contraction, with orientations. -/
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureExoticOverlapTwo
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open Holant Holant.Pauli.ExoticKlein
variable {P : Type*} [Fintype P] [LinearOrder P] {r : ℕ}

theorem one_cycle_labels_equal (M N : Matching P r) (fixed : Fin r → Label)
    (c : M.CycleHead N) (hc : M.cycleLength N c=1)
    (a b : Fin r → Label) (ha : M.overlap N fixed a≠0) (hb : M.overlap N fixed b≠0)
    (i : Fin (M.cycleLength N c)) :
    M.cycleLabels N a ⟨c,i⟩=M.cycleLabels N b ⟨c,i⟩ := by
  classical
  let localValue : (Fin (M.cycleLength N c) → Label) → ℂ :=
    cycleContraction (M.cycleLength N c)
      (fun i => fixed ((M.nCoordinates N).edges ⟨c,i⟩))
      (fun i => (M.mCoordinates N).reverse ⟨c,i⟩)
      (fun i => (M.nCoordinates N).reverse ⟨c,i⟩)
  have hcount : Fintype.card {v : Fin (M.cycleLength N c) → Label // localValue v≠0}=1 := by
    have hh := cycleContraction_support_card (M.cycleLength N c) (M.cycleLength_pos N c)
      (fun i => fixed ((M.nCoordinates N).edges ⟨c,i⟩))
      (fun i => (M.mCoordinates N).reverse ⟨c,i⟩)
      (fun i => (M.nCoordinates N).reverse ⟨c,i⟩)
    simpa only [hc,Nat.sub_self,pow_zero] using hh
  have hlive (v : Fin r → Label) (hv : M.overlap N fixed v≠0) :
      localValue (fun j => M.cycleLabels N v ⟨c,j⟩)≠0 := by
    rw [M.overlap_eq_cycleFamily N,cycleFamilyContraction_eq_prod] at hv
    exact (Finset.prod_ne_zero_iff.mp hv) c (Finset.mem_univ c)
  obtain ⟨u,hu⟩ := Fintype.card_eq_one_iff.mp hcount
  have he : (⟨(fun j => M.cycleLabels N a ⟨c,j⟩),hlive a ha⟩ :
      {v : Fin (M.cycleLength N c) → Label // localValue v≠0}) =
      ⟨(fun j => M.cycleLabels N b ⟨c,j⟩),hlive b hb⟩ :=
    (hu _).trans (hu _).symm
  exact congrFun (congrArg Subtype.val he) i

/-- Outside the two literal M edges of the unique nontrivial cycle, all live
coefficient words have exactly the SAME labels. -/
theorem overlap_four_only_two (M N : Matching P r) (fixed : Fin r → Label)
    (hfour : Fintype.card {a : Fin r → Label // M.overlap N fixed a≠0}=4) :
    ∃ e f : Fin r, e≠f ∧ ∀ a b : Fin r → Label,
      M.overlap N fixed a≠0 → M.overlap N fixed b≠0 →
      ∀ j, j≠e → j≠f → a j=b j := by
  classical
  obtain ⟨c,hc,hother⟩ := M.support_four_cycle_shape N fixed hfour
  let i0 : Fin (M.cycleLength N c) := ⟨0,by omega⟩
  let i1 : Fin (M.cycleLength N c) := ⟨1,by omega⟩
  let edges := (M.mCoordinates N).edges
  let e := edges ⟨c,i0⟩
  let f := edges ⟨c,i1⟩
  have hef : e≠f := by
    intro h
    have he := edges.injective h
    have hv := congrArg (fun q : M.CycleEdge N => q.2.val) he
    dsimp [i0,i1] at hv
    omega
  refine ⟨e,f,hef,?_⟩
  intro a b ha hb j hje hjf
  obtain ⟨⟨d,k⟩,rfl⟩ := edges.surjective j
  have hdc : d≠c := by
    intro he
    subst d
    have hk : k=i0 ∨ k=i1 := by
      have hv : k.val < M.cycleLength N c := k.isLt
      have h0 : i0.val=0 := rfl
      have h1 : i1.val=1 := rfl
      by_cases hz : k.val=0
      · exact Or.inl (Fin.ext (hz.trans h0.symm))
      · exact Or.inr (Fin.ext (by omega))
    rcases hk with hk | hk
    · exact hje (congrArg (fun z => edges ⟨c,z⟩) hk)
    · exact hjf (congrArg (fun z => edges ⟨c,z⟩) hk)
  exact one_cycle_labels_equal M N fixed d (hother d hdc) a b ha hb k

end
end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureExoticOverlapTwo
