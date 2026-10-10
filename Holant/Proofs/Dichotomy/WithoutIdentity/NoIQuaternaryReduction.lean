import Holant.Proofs.Dichotomy.Main.PaperTerminalBridgeSparseSource
import Holant.Proofs.Dichotomy.Main.PaperTerminalBridgeDenseControlled
import Holant.Proofs.Dichotomy.Main.PaperTerminalBridgeOneSidedIdentity
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIAnchorConsumer

/-! Exhaustive original no-I endpoint reduction. The only unconsumed source
classes are pure weighted equality and an actual complementary quaternary. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIQuaternaryReduction
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.Hardness.EightVertexNonexception
namespace A
export GlobalCloseCompletionUnaryDescentSource (ambient)
end A
namespace S
export PaperTerminalBridgeDenseSemantic (family)
end S
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option Elab.async false
variable {s degree : ℕ} {a : ℕ→ℕ}
variable (L : IntermediateField ℚ AlgebraicComplex)
local instance : Algebra ℚ L:=L.algebra'
variable (H : (i : Fin s)→Signature L (a i.val)) (F : FixedField L degree)
variable (q : Signature L 4) (label : Fin s)
variable (literal : (⟨a label.val,H label⟩ : AnySignature L)=⟨4,q⟩)
variable (even : EvenSupport q) (first : (entries q).a≠0) (last : (entries q).x≠0)

abbrev Outcome := PaperTerminalBridgeSparseSource.Outcome L H F q

include literal even first last in
theorem source : Outcome L H F q := by
  classical
  letI : NumberField L:={to_charZero:=inferInstance,to_finiteDimensional:=F.basis.finiteDimensional_of_finite}
  by_cases zero : PaperTerminalBridgeSparseCanonical.SomeZero (entries q)
  · exact PaperTerminalBridgeSparseSource.source L H F q label literal even first last zero
  have dense : StableDenseParityAlgebra.Dense q := by
    unfold PaperTerminalBridgeSparseCanonical.SomeZero at zero
    push_neg at zero
    exact ⟨first,zero.1,zero.2.1,zero.2.2.1,zero.2.2.2.1,zero.2.2.2.2.1,zero.2.2.2.2.2,last⟩
  rcases PaperTerminalBridgeDenseControlled.source H F L.subtype q label literal even dense with hard|oneSided|anchor|comp
  · exact Or.inr (Or.inl hard)
  · rcases NoISuppliedIdentityConsumer.tract_or_hard L H F
        (PaperTerminalBridgeOneSidedIdentity.produce L H F q label literal even dense oneSided) with good|hard
    · exact Or.inl good
    · exact Or.inr (Or.inl hard)
  · have mapped : RingHomRealization.mapFamily L.subtype (S.family H)=A.ambient L H := by
      ext f
      constructor
      · rintro ⟨g,⟨i,rfl⟩,rfl⟩;exact ⟨i,rfl⟩
      · rintro ⟨i,rfl⟩;exact ⟨_,⟨i,rfl⟩,rfl⟩
    rw [mapped] at anchor
    rcases NoIAnchorConsumer.classified L H F anchor with good|hard
    · exact Or.inl good.tract
    · exact Or.inr (Or.inl hard)
  · obtain ⟨g,actual,evenG,denseG,compG⟩:=comp
    exact Or.inr (Or.inr (Or.inr ⟨g,actual,evenG,denseG.1,denseG.2.2.2.2.2.2.2,compG⟩))

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIQuaternaryReduction
end
