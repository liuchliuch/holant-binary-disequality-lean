import Holant.Certificates.MatchingProductBridge.ConeEmbedding
import Holant.Certificates.MatchingProductBridge.GroupInverses
import Holant.Certificates.MatchingProductBridge.InvertibleBridgeNecessity

namespace Holant.Certificates.MatchingProductBridge
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The source R construction uses the actual matrix inverse transpose. -/
def matrixR (U : Binary) : FourTensor := (1/2 : ℂ) • P2 U (binaryInverseTranspose U)

/-- Nonexceptional actual-cone membership retains a symmetric direction in the same concrete group. -/
theorem concrete_bridge_necessity (g : PlatonicModel) (W : FourTensor) (h : bridgeConditions g W) :
    W = 0 ∨ W = (1/2 : ℂ) • A ∨ W = (1/2 : ℂ) • B ∨
      ∃ U : Binary, groupDirection g U ∧ transpose U = U ∧ W = matrixR U := by
  rcases matchingCone_presentation g W h.1 with hW | ⟨r,U,V,hU,hV,hW⟩
  · exact Or.inl hW
  rcases matchingCone_presentation g (A-(2:ℂ)•W) h.2.1 with hA | ⟨s,L,M,hL,hM,hA⟩
  · right; left
    have he := sub_eq_zero.mp hA
    calc W = (1/2 : ℂ) • ((2:ℂ) • W) := by module
      _ = (1/2 : ℂ) • A := by rw [← he]
  rcases matchingCone_presentation g ((2:ℂ)•W-B) h.2.2 with hB | ⟨t,N,P,hN,hP,hB⟩
  · right; right; left
    have he := sub_eq_zero.mp hB
    calc W = (1/2 : ℂ) • ((2:ℂ) • W) := by module
      _ = (1/2 : ℂ) • B := by rw [he]
  have hr : InvertibleMatching r W := ⟨U,V,groupDirection_det_ne_zero g hU,groupDirection_det_ne_zero g hV,hW⟩
  have hs : InvertibleMatching s (A-(2:ℂ)•W) := ⟨L,M,groupDirection_det_ne_zero g hL,groupDirection_det_ne_zero g hM,hA⟩
  have ht : InvertibleMatching t ((2:ℂ)•W-B) := ⟨N,P,groupDirection_det_ne_zero g hN,groupDirection_det_ne_zero g hP,hB⟩
  have hdet : Matrix.det U ≠ 0 := groupDirection_det_ne_zero g hU
  have hi := invertible_bridge_matching_indices W r s t hr hs ht
  rcases hi with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
  · have hW' : (2:ℂ)•W = P0 U ((2:ℂ)•V) := by rw [hW]; funext x; simp [matchingTensor,P0,smul_eq_mul]; ring
    have ha : (flatten0 (A-P0 U ((2:ℂ)•V))).rank = 1 := by simpa [hW',flatten] using hs.rank 0
    have hb : (flatten2 (P0 U ((2:ℂ)•V)-B)).rank = 1 := by simpa [hW',flatten] using ht.rank 2
    have he := matching0_bridge_exceptional U ((2:ℂ)•V) hdet ha hb
    right; left
    calc W = (1/2 : ℂ) • ((2:ℂ) • W) := by module
      _ = (1/2 : ℂ) • A := by rw [hW',he]
  · have hW' : (2:ℂ)•W = P1 U ((2:ℂ)•V) := by rw [hW]; funext x; simp [matchingTensor,P1,smul_eq_mul]; ring
    have ha : (flatten2 (A-P1 U ((2:ℂ)•V))).rank = 1 := by simpa [hW',flatten] using hs.rank 2
    have hb : (flatten1 (P1 U ((2:ℂ)•V)-B)).rank = 1 := by simpa [hW',flatten] using ht.rank 1
    have he := matching1_bridge_exceptional U ((2:ℂ)•V) hdet ha hb
    right; right; left
    calc W = (1/2 : ℂ) • ((2:ℂ) • W) := by module
      _ = (1/2 : ℂ) • B := by rw [hW',he]
  · have hW' : W = P2 U V := by simpa [matchingTensor] using hW
    have ha : (flatten1 (A-(2:ℂ)•P2 U V)).rank = 1 := by simpa [hW',flatten] using hs.rank 1
    have hb : (flatten0 ((2:ℂ)•P2 U V-B)).rank = 1 := by simpa [hW',flatten] using ht.rank 0
    obtain ⟨hv,hu⟩ := matching2_scaled_bridge_factors U V hdet ha hb
    right; right; right
    refine ⟨U,hU,hu,?_⟩
    have ho : Matrix.of U = U := rfl
    rw [hW',hv]
    funext x
    simp [matrixR,P2,binaryInverseTranspose,binaryInverse,transpose,smul_eq_mul,ho]
    ring

end
end Holant.Certificates.MatchingProductBridge
