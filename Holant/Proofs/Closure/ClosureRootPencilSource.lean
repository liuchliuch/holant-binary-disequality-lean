import Holant.Proofs.Closure.ClosureRootPencilProduct
import Holant.Proofs.Closure.ClosureSixPortParity

/-! Exact bridge from the raw six-port endpoint root deck to the normalized
four-port actual product. No matching or ruling conclusion is a premise. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureRootPencil
open Holant Holant.Projective

theorem rootMatching_iff_product (m : ℕ) (q : Signature ℂ 4) :
    ClosureSixPort.RootMatching m q ↔ RootProduct m q := by
  constructor
  · rintro ⟨M,mono,scalar,equation⟩
    exact of_presentation M mono scalar equation
  · rintro ⟨D⟩
    exact ⟨⟨2,D.ports,D.matrix,D.scalar⟩,D.rooted,D.nonzero,D.equation⟩

theorem rootMatching_support_card {m : ℕ} {q : Signature ℂ 4}
    (actual : ClosureSixPort.RootMatching m q) : (support q).card=4 := by
  obtain ⟨D⟩ := (rootMatching_iff_product m q).mp actual
  exact D.support_card

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureRootPencil
