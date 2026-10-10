import Holant.Proofs.Hardness.GeneralEODEQProducerSupportInterval
import Holant.Proofs.Hardness.GeneralEODEQProducerSupportMoves

/-! The combinatorial DEQ obstruction from a failure of odd-XOR purity.
The proof constructs an isolated support interval of distance at least four.
It uses finite interval descent and a strictly decreasing zero-moving measure;
no support-completeness, gadget, or hardness hypothesis is supplied. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEODEQProducerSupport
open Holant Holant.Tractable
namespace B
export GeneralEODEQProducerSupportBasic (Pure xorList)
end B
namespace C
export GeneralEODEQProducerCore (Pair)
end C
namespace I
export GeneralEODEQProducerSupportInterval (exists_twoFlip)
end I
namespace M
export GeneralEODEQProducerSupportMoves
  (positive_pure_of_descent dual dual_central dual_supports pair_of_dual negative_pure_of_dual)
end M
variable {n : ℕ} {f : Signature AlgebraicComplex n}

/-- Absence of a two-point interval of distance at least four forces purity
on the side chosen by the ternary support condition. -/
theorem pure_of_no_pair (sign : EOSign) (he : Signature.CentralSupport f)
    (hs : EONegativeWitness.Supports sign ⟨n,f⟩)
    (hn : ¬Nonempty (C.Pair f)) : B.Pure sign f := by
  cases sign with
  | positive =>
    apply M.positive_pure_of_descent he hs
    intro a b δ ha hb hg
    exact I.exists_twoFlip f he hn δ a b ha hb hg
  | negative =>
    apply M.negative_pure_of_dual
    apply M.positive_pure_of_descent (M.dual_central he) (M.dual_supports hs)
    intro a b δ ha hb hg
    apply I.exists_twoFlip (M.dual f) (M.dual_central he) _ δ a b ha hb hg
    rintro ⟨P⟩
    exact hn ⟨M.pair_of_dual P⟩

/-- Literal support hypotheses produce the isolated interval consumed by the
physical pinning and self-loop DEQ4 construction. -/
theorem exists_pair (sign : EOSign) (he : Signature.CentralSupport f)
    (hs : EONegativeWitness.Supports sign ⟨n,f⟩)
    (hp : ¬B.Pure sign f) : Nonempty (C.Pair f) := by
  by_contra hn
  exact hp (pure_of_no_pair sign he hs hn)

/-- The producer returns the original supported words and their literal
coordinate interval, rather than a preselected or assumed gadget. -/
theorem exists_isolated_interval (sign : EOSign) (he : Signature.CentralSupport f)
    (hs : EONegativeWitness.Supports sign ⟨n,f⟩)
    (hp : ¬B.Pure sign f) :
    ∃ a b : Fin n → Bool, f a ≠ 0 ∧ f b ≠ 0 ∧
      4 ≤ GeneralEOPhaseExtractionDistance.distance a b ∧
      (∀ x, f x ≠ 0 → (∀ i, a i = b i → x i = a i) → x = a ∨ x = b) := by
  obtain ⟨P⟩ := exists_pair sign he hs hp
  exact ⟨P.left,P.right,P.left_supported,P.right_supported,P.distant,P.isolated⟩

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEODEQProducerSupport
