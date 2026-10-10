import Holant.Proofs.Dichotomy.Main.PaperTerminalBridgeDenseSemantic
import Holant.Proofs.Dichotomy.Main.PaperTerminalBridgeEqualProductsAnchor
import Holant.Proofs.Dichotomy.Main.PaperTerminalBridgeEqualProductsMiddleComplement

/-! Exhaustive dense endpoint producer over the unchanged finite source.
Actual infinite antidiagonal ratios are consumed by counting hardness; finite
ratios supply their own complete cyclic deck and actual complementary normal
form. Singular antidiagonals and equality anchors remain explicit physical
outputs for their separate whole-family consumers. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperTerminalBridgeDenseSource
open Computability Holant Holant.Algebraic Holant.Complexity Holant.Tractable
open Holant.LocalDrafts.Hardness.EightVertexNonexception
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
namespace S
export NativeAntiTargetSource (base)
export PaperTerminalBridgeDenseSemantic (family)
end S
namespace A
export PaperTerminalBridgeAntiGroup (Available)
end A
namespace C
export GeneralCancellationCapPin (antiTensor)
end C
namespace D
export PaperTerminalBridgeFiniteDeck (NoOneSided classification)
end D
namespace RH
export Holant.LocalDrafts.MainChain.RingHomRealization (mapFamily)
end RH
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option Elab.async false
variable {K : Type} [Field K] [NumberField K] {s degree : ℕ} {a : ℕ→ℕ}
variable (H : (i : Fin s)→Signature K (a i.val)) (F : FixedField K degree)
variable (phi : K→+*AlgebraicComplex)

def OneSided (family : SignatureFamily K) : Prop :=
  ∃p q : K,Gadget.RealizesUpTo family .disequality (C.antiTensor p q) ∧
    ((p=0 ∧ q≠0) ∨ (p≠0 ∧ q=0))

def ComplementOutput (family : SignatureFamily K) : Prop :=
  ∃g : Signature K 4,Gadget.RealizesUpTo family .disequality g ∧
    EvenSupport g ∧ StableDenseParityAlgebra.Dense g ∧ PaperTerminalBridgeComplementSign.Complement g

def Outcome : Prop :=
  Holant.LocalDrafts.CountingHardness.WitnessCountingHard
    (RawClosedNetwork.validatedEncoding s 1 a) F.encoding ((S.base H F).evaluate F) ∨
  OneSided (S.family H) ∨
  Holant.EightVertex.ProductAnchor.HasEqualityAnchor (RH.mapFamily phi (S.family H)) ∨
  ComplementOutput (S.family H)

theorem oneSided_of_not_safe (family : SignatureFamily K) (bad : ¬D.NoOneSided family) :
    OneSided family := by
  classical
  unfold D.NoOneSided at bad
  push Not at bad
  obtain ⟨p,q,actual,bad⟩ := bad
  exact ⟨p,q,actual,bad⟩

theorem source (q : Signature K 4) (label : Fin s)
    (literal : (⟨a label.val,H label⟩ : AnySignature K)=⟨4,q⟩)
    (even : EvenSupport q) (dense : StableDenseParityAlgebra.Dense q) : Outcome H F phi := by
  classical
  have actual : Gadget.Realizes (S.family H) .disequality q :=
    Gadget.realizes_of_mem _ _ _ ⟨label,literal⟩
  by_cases products : PaperTerminalBridgeDenseOrders.EqualProducts q
  · exact Or.inr (Or.inr (Or.inl
      (PaperTerminalBridgeEqualProductsAnchor.source phi (S.family H) q actual even dense products)))
  by_cases safe : D.NoOneSided (S.family H)
  · by_cases torsion : ∀t : K,A.Available (S.family H) t→t≠0→IsOfFinOrder t
    · rcases D.classification (S.family H) (PaperTerminalBridgeCancellationField.embedding (K:=K)).toRingHom
          q actual even dense safe torsion with middle | complementary
      · exact Or.inr (Or.inr (Or.inr
          (PaperTerminalBridgeEqualProductsMiddleComplement.source phi (S.family H) q actual even dense middle)))
      · obtain ⟨ε,square,b,c,d⟩ := complementary
        exact Or.inr (Or.inr (Or.inr
          (PaperTerminalBridgeComplementSign.source (S.family H) q actual even dense ε square b c d)))
    · push Not at torsion
      obtain ⟨t,act,nonzero,infinite⟩ := torsion
      exact Or.inl (PaperTerminalBridgeDenseSemantic.countingHard H F q label literal even dense products
        t nonzero act infinite)
  · exact Or.inr (Or.inl (oneSided_of_not_safe (S.family H) safe))

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperTerminalBridgeDenseSource
end
