import Holant.ReedMuller.Steiner.Reconstruction

namespace Holant.ReedMuller.Steiner
open Holant.ReedMuller.LowArity Holant.ReedMuller.CoefficientAtlas
noncomputable section
variable {n : ℕ}

/-- The manuscript's wording in actual binary codewords, rather than sets. -/
def WordSteinerProperty (D : BinaryCode n) : Prop :=
  ∀ a b c : Fin n,a≠b → a≠c → b≠c →
    ∃! w : BinaryVector n,w∈D ∧ (support w).card=4 ∧ a∈support w ∧ b∈support w ∧ c∈support w

theorem word_steiner_iff (D : BinaryCode n) : WordSteinerProperty D ↔ SteinerProperty D := by
  constructor
  · intro h a b c hab hac hbc
    obtain ⟨w,hw,hu⟩ := h a b c hab hac hbc
    refine ⟨support w,⟨⟨hw.2.1,by simpa only [indicator_support] using hw.1⟩,
      hw.2.2.1,hw.2.2.2.1,hw.2.2.2.2⟩,?_⟩
    intro B hB
    have H := hu (indicator B) (by simpa only [support_indicator] using
      (show indicator B∈D ∧ B.card=4 ∧ a∈B ∧ b∈B ∧ c∈B from
        ⟨hB.1.2,hB.1.1,hB.2.1,hB.2.2.1,hB.2.2.2⟩))
    simpa only [support_indicator] using congrArg support H
  · intro h a b c hab hac hbc
    obtain ⟨B,hB,hu⟩ := h a b c hab hac hbc
    refine ⟨indicator B,?_,?_⟩
    · simpa only [support_indicator] using
        (show indicator B∈D ∧ B.card=4 ∧ a∈B ∧ b∈B ∧ c∈B from
          ⟨hB.1.2,hB.1.1,hB.2.1,hB.2.2.1,hB.2.2.2⟩)
    · intro w hw
      have H := hu (support w) ⟨⟨hw.2.1,by simpa only [indicator_support] using hw.1⟩,
        hw.2.2.1,hw.2.2.2.1,hw.2.2.2.2⟩
      simpa only [indicator_support] using congrArg indicator H

theorem point_coordinates_bijective : Function.Bijective pointBit := by decide

/-- Source Lemma6.17, retaining its original no-weight-two hypothesis. The
coordinate identification is explicit and RM is the actual evaluation code. -/
theorem source_self_dual_steiner_reconstruction (D : BinaryCode n) (hn : 4<n)
    (hD : SelfDual D) (_hno : ∀ x : BinaryVector n,x∈D → (support x).card≠2)
    (hS : WordSteinerProperty D) :
    n=8 ∧ ∃ e : Point ≃ Fin n,∀ x : BinaryVector n,
      x∈D ↔ (fun p => x (e p))∈code :=
  steiner_reconstruction D hn hD ((word_steiner_iff D).mp hS)

end
end Holant.ReedMuller.Steiner
