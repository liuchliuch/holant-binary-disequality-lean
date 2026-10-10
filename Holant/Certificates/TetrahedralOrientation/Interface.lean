import Holant.Certificates.TetrahedralOrientation.Resources
import Holant.Certificates.TetrahedralOrientation.Ranks

/-! Full current Proposition A.17, including literal reconstruction, original
physical port order, actual tetrahedral binaries, and all three matrix ranks. -/
namespace Holant.Certificates.TetrahedralOrientation
open Holant Holant.Certificates.MatchingProductBridge
noncomputable section

def ExceptionalOrientation (τ : Fin 3 → Fin 4) : Prop :=
  τ = ![0,3,1] ∨ τ = ![1,0,3] ∨ τ = ![3,1,0]

theorem sigma_exceptional (s : Orientation) : ExceptionalOrientation (sigma s) := by
  fin_cases s
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

theorem exceptional_iff (τ : Fin 3 → Fin 4) :
    ExceptionalOrientation τ ↔ ∃ s : Orientation, τ = sigma s := by
  constructor
  · rintro (h | h | h)
    · exact ⟨0,h⟩
    · exact ⟨1,h⟩
    · exact ⟨2,h⟩
  · rintro ⟨s,rfl⟩
    exact sigma_exceptional s

/-- All source claims retain the actual tensors and the exact physical scalar. -/
structure TerminalCertificate (s : Orientation) : Prop where
  original_contraction : card s = Signature.contract Q0 (Tensor.reindex contractOrder (ancestor s))
  contraction_graph : (cardNetwork s).denote = card s
  actual_legs : ∀ j, groupDirection .tetrahedral (multiply (nativeLeg (legs s j)) X)
  invertible_legs : ∀ j, Matrix.det (Matrix.of (legs s j)) ≠ 0
  exact_dressing : dressed s = Signature.coordinateAction (legs s) (card s)
  physical_graph : (terminalNetwork s).denote = dressed s
  actual_realization : Gadget.Realizes (tetrahedralResources s) .disequality (dressed s)
  exact_table : dressed s = rawScale s • terminal s
  physical_scalar_nonzero : rawScale s ≠ 0
  eight_vertex : EndpointNondegenerateEightVertex (dressed s)
  ranks_before : ∀ r : Fin 3, (flatten r (card s)).rank = 2
  ranks_after : ∀ r : Fin 3, (flatten r (dressed s)).rank = 2

/-- Proposition A.17: all three exceptional orientations have actual tetrahedral
port dressings to endpoint-nondegenerate eight-vertex signatures, retaining rank222. -/
theorem tetrahedral_permutation_classes (s : Orientation) : TerminalCertificate s where
  original_contraction := rfl
  contraction_graph := cardNetwork_denote s
  actual_legs := nativeLeg_actual s
  invertible_legs := legs_nonsingular s
  exact_dressing := rfl
  physical_graph := terminalNetwork_denote s
  actual_realization := dressed_realizes s
  exact_table := dressed_exact s
  physical_scalar_nonzero := rawScale_ne_zero s
  eight_vertex := dressed_eightVertex s
  ranks_before := card_rank_two s
  ranks_after := dressed_rank_two s

theorem every_exceptional_orientation (τ : Fin 3 → Fin 4) (h : ExceptionalOrientation τ) :
    ∃ s : Orientation, τ = sigma s ∧ TerminalCertificate s := by
  obtain ⟨s,hs⟩ := (exceptional_iff τ).mp h
  exact ⟨s,hs,tetrahedral_permutation_classes s⟩

end
end Holant.Certificates.TetrahedralOrientation
