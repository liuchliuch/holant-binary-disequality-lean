import Holant.Pauli.ExoticKlein.MatchingContraction
import Holant.Pauli.ExoticKlein.CycleContractionFamily

/-! Exact arbitrary-matching support size, derived from the original port
contraction and the canonical alternating-cycle decomposition. -/
namespace Holant.Pauli.ExoticKlein
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace Matching
variable {P : Type*} {r : ℕ} [Fintype P] [LinearOrder P]

 def cycleLength (M N : Matching P r) (c : M.CycleHead N) : ℕ := (M.orbitSet N c.val).card

 def cycleCount (M N : Matching P r) : ℕ := Fintype.card (M.CycleHead N)

 theorem cycleLength_pos (M N : Matching P r) (c : M.CycleHead N) : 0 < M.cycleLength N c :=
  Finset.card_pos.mpr (M.orbitSet_nonempty N c.val)

 theorem sum_cycleLength (M N : Matching P r) : ∑ c, M.cycleLength N c = r := by
  have h := M.card_cycleEdge N
  change Fintype.card (Sigma (fun c : M.CycleHead N => Fin (M.cycleLength N c))) = r at h
  simpa only [Fintype.card_sigma,Fintype.card_fin] using h

 def cycleLabels (M N : Matching P r) : (Fin r → Label) ≃ (M.CycleEdge N → Label) where
  toFun a e := a ((M.mCoordinates N).edges e)
  invFun a e := a ((M.mCoordinates N).edges.symm e)
  left_inv a := by funext e; simp only [Equiv.apply_symm_apply]
  right_inv a := by funext e; simp only [Equiv.symm_apply_apply]

 theorem overlap_eq_cycleFamily (M N : Matching P r) (fixed labels : Fin r → Label) :
    M.overlap N fixed labels = cycleFamilyContraction (M.cycleLength N)
      (fun e => fixed ((M.nCoordinates N).edges e))
      (M.mCoordinates N).reverse (M.nCoordinates N).reverse (M.cycleLabels N labels) := by
  unfold cycleFamilyContraction
  exact M.overlap_eq_cycle_sum N fixed labels

/-- Lemma8.4: an actual N-matching product has exactly 4^(r-c) nonzero
coefficients in the actual M-dual basis. Common edges count as cycles. -/
 theorem overlap_support_card (M N : Matching P r) (fixed : Fin r → Label) :
    Fintype.card {labels : Fin r → Label // M.overlap N fixed labels ≠ 0} =
      4^(r-M.cycleCount N) := by
  let e : {labels : Fin r → Label // M.overlap N fixed labels ≠ 0} ≃
      {labels : M.CycleEdge N → Label // cycleFamilyContraction (M.cycleLength N)
        (fun e => fixed ((M.nCoordinates N).edges e))
        (M.mCoordinates N).reverse (M.nCoordinates N).reverse labels ≠ 0} :=
    (M.cycleLabels N).subtypeEquiv (fun labels =>
    show M.overlap N fixed labels ≠ 0 ↔ cycleFamilyContraction (M.cycleLength N)
      (fun e => fixed ((M.nCoordinates N).edges e))
      (M.mCoordinates N).reverse (M.nCoordinates N).reverse (M.cycleLabels N labels) ≠ 0 from
      by rw [M.overlap_eq_cycleFamily N])
  rw [Fintype.card_congr e]
  have hc := cycleFamilyContraction_support_card (M.cycleLength N) (M.cycleLength_pos N)
    (fun e => fixed ((M.nCoordinates N).edges e))
    (M.mCoordinates N).reverse (M.nCoordinates N).reverse
  rw [M.sum_cycleLength N] at hc
  exact hc

 theorem scaled_overlap_support_card (M N : Matching P r) (fixed : Fin r → Label)
    (s : ℂ) (hs : s ≠ 0) :
    Fintype.card {labels : Fin r → Label // M.coefficient (fun x => s*N.tensor fixed x) labels ≠ 0} =
      4^(r-M.cycleCount N) := by
  have hc : ∀ labels, M.coefficient (fun x => s*N.tensor fixed x) labels = s*M.overlap N fixed labels := by
    intro labels
    simp only [coefficient,overlap,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    ring
  let e := Equiv.subtypeEquivRight (fun labels =>
    show M.coefficient (fun x => s*N.tensor fixed x) labels ≠ 0 ↔ M.overlap N fixed labels ≠ 0 by
      rw [hc]; simp [hs])
  rw [Fintype.card_congr e,M.overlap_support_card N]

end Matching
end
end Holant.Pauli.ExoticKlein
