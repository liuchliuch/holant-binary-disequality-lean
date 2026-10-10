import Holant.Proofs.Hardness.GeneralEOPhaseExtractionSelfdualAlternative
import Holant.Proofs.Hardness.GeneralEOPhaseExtractionSelfdualFieldBridge
import Holant.Proofs.Hardness.GeneralEOPhaseControlledSelfdualQuaternary

/-! Arbitrary-arity selfdual non-ARS alternative: actual original pin
elimination, actual original length-controlled counting hardness, or a realized nonzero signed
tensor square. The final outcome is not asserted to be a signed binary gadget. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseControlledSelfdualAlternative
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity FixedGadgetSubstitution
namespace F
export GeneralEOPhaseExtractionSelfdualFieldBridge (nonpositive_quaternary)
end F
namespace S
export GeneralEOPhaseExtractionSource (inclusion)
export GeneralEOPhaseExtractionControlledSource (ControlledCountingHard)
end S
namespace Q
export GeneralEOPhaseExtractionSelfdualQuaternary (product)
end Q
namespace P
export GeneralEOPhaseExtractionMatchingSwitch (PositivePattern)
end P
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {s n : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))

export GeneralEOPhaseExtractionSelfdualAlternative (positive_image)

/-- All conclusions retain the unchanged original dictionary and field.
The signed tensor-square branch retains the physical graph and its scalar. -/
theorem pinning_hardness_or_signed_square (S0 : Network AlgebraicComplex n)
    (SL : Labelling S0.shape s 1 a) (hL : LabelledNetwork.Exact G S0 SL)
    (hN : ∀e,S0.edge e=Signature.disequality) (hE : Signature.CentralSupport S0.denote)
    (hS : SelfDualPinObstruction.SelfDual (S0.map S.inclusion).denote)
    (hA : ¬GeneralEOARSBoundary.ARSUpToScale (S0.map S.inclusion).denote) :
    Nonempty (GeneralEOPinEliminationCases.Elimination G) ∨ S.ControlledCountingHard G ∨
    ∃ (Q0 : Network AlgebraicComplex 4) (QL : Labelling Q0.shape s 1 a)
      (e : Equiv.Perm (Fin 4)) (c : AlgebraicComplex),
      LabelledNetwork.Exact G Q0 QL ∧ (∀i,Q0.edge i=Signature.disequality) ∧ c≠0 ∧
      Tensor.reindex e Q0.denote=EOBinaryPlaneCore.lift (Q.product c true) := by
  obtain ⟨N,NL,hNL,hNN,hNE,hNS,hNP⟩ := F.nonpositive_quaternary G S.inclusion
    S0 SL hL hN hE hS hA
  rcases GeneralEOPhaseControlledSelfdualQuaternary.pinning_hardness_or_product G N NL hNL hNN hNE hNS
    with hp|hh|hr
  · exact Or.inl hp
  · exact Or.inr (Or.inl hh)
  obtain ⟨e,hplane,hzero|⟨c,hc,b,hb⟩⟩ := hr
  · exfalso
    apply hNP (positive_image N e 0 ?_)
    rw [hplane,hzero]
    congr 1
  · cases b
    · exact False.elim (hNP (positive_image N e c (hplane.trans (congrArg EOBinaryPlaneCore.lift hb))))
    · exact Or.inr (Or.inr ⟨N,NL,e,c,hNL,hNN,hc,hplane.trans (congrArg EOBinaryPlaneCore.lift hb)⟩)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseControlledSelfdualAlternative
