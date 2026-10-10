import Holant.Pauli.ExoticKlein.MatchingFour

/-! A nonzero exotic matching tensor determines its actual unoriented ruling.
Equality of mate involutions records the original physical pairs and ignores
only the irrelevant enumeration/orientation of matching edges. -/
namespace Holant.Pauli.ExoticKlein
noncomputable section
open scoped BigOperators
namespace Matching
variable {P : Type*} {r : ℕ} [Fintype P] [LinearOrder P]

theorem support_one_cycle_lengths (M N : Matching P r) (fixed : Fin r → Label)
    (h : Fintype.card {labels : Fin r → Label // M.overlap N fixed labels ≠ 0} = 1) :
    ∀ c : M.CycleHead N, M.cycleLength N c = 1 := by
  rw [M.overlap_support_card N] at h
  have hexp : r-M.cycleCount N = 0 :=
    Nat.pow_right_injective (by decide : 2 ≤ 4) (by simpa using h)
  have hsum : ∑ c, (M.cycleLength N c-1) = 0 := by rw [M.sum_cycle_extras N,hexp]
  intro c
  have hle : M.cycleLength N c-1 ≤ ∑ d, (M.cycleLength N d-1) :=
    Finset.single_le_sum (f := fun d => M.cycleLength N d-1) (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
  have hpos := M.cycleLength_pos N c
  omega

theorem mate_eq_of_cycle_lengths (M N : Matching P r)
    (hlen : ∀ c : M.CycleHead N, M.cycleLength N c = 1) : M.mate = N.mate := by
  have hnext (e : M.CycleEdge N) : M.cycleNext N e = e := by
    rcases e with ⟨c,i⟩
    change (⟨c,finRotate _ i⟩ : M.CycleEdge N) = ⟨c,i⟩
    congr 1
    apply Fin.ext
    have hi := i.isLt
    have hj := (finRotate _ i).isLt
    change i.val < M.cycleLength N c at hi
    change (finRotate _ i).val < M.cycleLength N c at hj
    rw [hlen c] at hi hj
    omega
  have hN (e : M.CycleEdge N) :
      N.mate (M.canonicalPorts N (e,true)) = M.canonicalPorts N (e,false) := by
    rw [M.canonicalPorts_Nmate N,hnext]
  ext p
  obtain ⟨⟨e,b⟩,rfl⟩ := (M.canonicalPorts N).surjective p
  cases b
  · rw [M.canonicalPorts_mate N]
    simpa only [Bool.not_false,N.mate_mate] using congrArg N.mate (hN e)
  · rw [M.canonicalPorts_mate N]
    exact (hN e).symm

/-- Projectively equal matching tensors pair precisely the same original ports. -/
theorem mate_eq_of_scaled_tensor (M N : Matching P r) (labels fixed : Fin r → Label)
    (s : ℂ) (hs : s ≠ 0) (he : M.tensor labels = fun x => s*N.tensor fixed x) :
    M.mate = N.mate := by
  have hc := M.scaled_overlap_support_card N fixed s hs
  rw [←he] at hc
  have hsingle : Fintype.card {a : Fin r → Label // M.coefficient (M.tensor labels) a ≠ 0} = 1 := by
    simp only [M.same_matching_coefficient]
    simp
  rw [hsingle] at hc
  have ho : Fintype.card {a : Fin r → Label // M.overlap N fixed a ≠ 0} = 1 := by
    rw [M.overlap_support_card N]
    exact hc.symm
  exact M.mate_eq_of_cycle_lengths N (M.support_one_cycle_lengths N fixed ho)

end Matching
end
end Holant.Pauli.ExoticKlein
