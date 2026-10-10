import Holant.Pauli.ExoticKlein.MatchingFour
import Holant.Pauli.ExoticKlein.CycleVariation

/-! The support-four refinement on the original matching's actual edge IDs. -/
namespace Holant.Pauli.ExoticKlein
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
namespace Matching
variable {P : Type*} {r : ℕ} [Fintype P] [LinearOrder P]

 def Varies (M N : Matching P r) (fixed : Fin r → Label) (edge : Fin r) : Prop :=
  ∃ a b : Fin r → Label, M.overlap N fixed a ≠ 0 ∧ M.overlap N fixed b ≠ 0 ∧ a edge ≠ b edge

 theorem varies_cycle_edge_iff (M N : Matching P r) (fixed : Fin r → Label) (e : M.CycleEdge N) :
    M.Varies N fixed ((M.mCoordinates N).edges e) ↔ 2 ≤ M.cycleLength N e.1 := by
  have h := cycleFamilyContraction_coordinate_varies_iff (M.cycleLength N) (M.cycleLength_pos N)
    (fun e => fixed ((M.nCoordinates N).edges e))
    (M.mCoordinates N).reverse (M.nCoordinates N).reverse e
  constructor
  · rintro ⟨a,b,ha,hb,hab⟩
    apply h.mp
    refine ⟨M.cycleLabels N a,M.cycleLabels N b,?_,?_,hab⟩
    · rwa [← M.overlap_eq_cycleFamily N]
    · rwa [← M.overlap_eq_cycleFamily N]
  · intro he
    obtain ⟨a,b,ha,hb,hab⟩ := h.mpr he
    refine ⟨(M.cycleLabels N).symm a,(M.cycleLabels N).symm b,?_,?_,?_⟩
    · rw [M.overlap_eq_cycleFamily N,Equiv.apply_symm_apply]
      exact ha
    · rw [M.overlap_eq_cycleFamily N,Equiv.apply_symm_apply]
      exact hb
    · change a ((M.mCoordinates N).edges.symm ((M.mCoordinates N).edges e)) ≠
        b ((M.mCoordinates N).edges.symm ((M.mCoordinates N).edges e))
      simpa only [Equiv.symm_apply_apply] using hab

/-- Every label appears at each varying original edge, with an actual nonzero
coefficient. This makes “varying” stronger than merely counting the support. -/
 theorem varying_edge_surjective (M N : Matching P r) (fixed : Fin r → Label) (e : M.CycleEdge N)
    (he : 2 ≤ M.cycleLength N e.1) (a : Label) :
    ∃ labels : Fin r → Label, M.overlap N fixed labels ≠ 0 ∧ labels ((M.mCoordinates N).edges e) = a := by
  obtain ⟨labels,hl,heq⟩ := cycleFamilyContraction_coordinate_surjective (M.cycleLength N)
    (M.cycleLength_pos N) (fun e => fixed ((M.nCoordinates N).edges e))
    (M.mCoordinates N).reverse (M.nCoordinates N).reverse e he a
  refine ⟨(M.cycleLabels N).symm labels,?_,?_⟩
  · rw [M.overlap_eq_cycleFamily N,Equiv.apply_symm_apply]
    exact hl
  · change labels ((M.mCoordinates N).edges.symm ((M.mCoordinates N).edges e)) = a
    simpa only [Equiv.symm_apply_apply] using heq

/-- The final assertion of Lemma8.4: exactly two distinct original M-edge IDs
vary when the coefficient support has cardinality four. -/
 theorem support_four_exactly_two_varying_edges (M N : Matching P r) (fixed : Fin r → Label)
    (h : Fintype.card {labels : Fin r → Label // M.overlap N fixed labels ≠ 0} = 4) :
    ∃ i j : Fin r, i ≠ j ∧ ∀ k, M.Varies N fixed k ↔ k = i ∨ k = j := by
  classical
  obtain ⟨c,hc,hrest⟩ := M.support_four_cycle_shape N fixed h
  let e0 : M.CycleEdge N := ⟨c,⟨0,by change 0 < M.cycleLength N c; omega⟩⟩
  let e1 : M.CycleEdge N := ⟨c,⟨1,by change 1 < M.cycleLength N c; omega⟩⟩
  have h01 : e0 ≠ e1 := by
    intro he
    have hn := congrArg (fun e : M.CycleEdge N => e.2.val) he
    change 0 = 1 at hn
    omega
  refine ⟨(M.mCoordinates N).edges e0,(M.mCoordinates N).edges e1,
    fun he => h01 ((M.mCoordinates N).edges.injective he),?_⟩
  intro k
  obtain ⟨e,rfl⟩ := (M.mCoordinates N).edges.surjective k
  rw [M.varies_cycle_edge_iff N]
  constructor
  · intro he
    have hec : e.1 = c := by
      by_contra hn
      have hh := hrest e.1 hn
      omega
    have hemem : e = e0 ∨ e = e1 := by
      cases e with | mk d i =>
        dsimp at hec
        subst d
        have hi : i.val = 0 ∨ i.val = 1 := by
          have hil := i.isLt
          change i.val < M.cycleLength N c at hil
          omega
        rcases hi with hi | hi
        · left
          have hi' : i = e0.2 := Fin.ext hi
          cases hi'
          rfl
        · right
          have hi' : i = e1.2 := Fin.ext hi
          cases hi'
          rfl
    exact hemem.imp (congrArg (M.mCoordinates N).edges) (congrArg (M.mCoordinates N).edges)
  · rintro (he | he)
    · have hh := (M.mCoordinates N).edges.injective he
      subst e
      exact le_of_eq hc.symm
    · have hh := (M.mCoordinates N).edges.injective he
      subst e
      exact le_of_eq hc.symm

end Matching
end
end Holant.Pauli.ExoticKlein
