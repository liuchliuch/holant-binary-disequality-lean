import Holant.Proofs.Dichotomy.Main.PaperTerminalBridgeSparseFinite
import Holant.Proofs.Dichotomy.Main.PaperTerminalBridgeSparseIdentity
import Holant.Proofs.Dichotomy.Main.PaperTerminalBridgeOneSidedSparseIdentity
import Holant.Proofs.Dichotomy.WithoutIdentity.NoISuppliedIdentityConsumer

/-! Exhaustive sparse no-I endpoint producer. Actual one-sided and infinite
antidiagonal branches are consumed into whole-family tractability or controlled
native counting hardness. Finite decks yield a genuinely realized complementary
q4. The pure weighted Eq4 branch is explicitly retained for its separate
whole-family replication consumer. No primeness or density shortcut is used. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperTerminalBridgeSparseSource
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.Hardness.EightVertexNonexception
namespace A
export GlobalCloseCompletionUnaryDescentSource (ambient)
export PaperTerminalBridgeAntiGroup (Available)
end A
namespace S
export PaperTerminalBridgeDenseSemantic (family)
end S
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
set_option Elab.async false
variable {s degree : ℕ} {a : ℕ→ℕ}
variable (L : IntermediateField ℚ AlgebraicComplex)
local instance : Algebra ℚ L:=L.algebra'
variable (H : (i : Fin s)→Signature L (a i.val)) (F : FixedField L degree)
variable (q : Signature L 4) (label : Fin s)
variable (literal : (⟨a label.val,H label⟩ : AnySignature L)=⟨4,q⟩)
variable (even : EvenSupport q) (first : (entries q).a≠0) (last : (entries q).x≠0)
variable (zero : PaperTerminalBridgeSparseCanonical.SomeZero (entries q))

def Outcome : Prop :=
  Tract (familyAction sourceKBasis (A.ambient L H)) ∨
  (NoISuppliedIdentityConsumer.target L H F).Hard ∨
  Holant.EightVertex.ProductAnchor.PureEquality (RingHomRealization.mapSignature L.subtype q) ∨
  PaperTerminalBridgeSparseNormalize.Output (S.family H)

include literal even first last zero in
theorem source : Outcome L H F q := by
  classical
  letI : NumberField L:={to_charZero:=inferInstance,to_finiteDimensional:=F.basis.finiteDimensional_of_finite}
  have completed (D : NoISuppliedIdentityData.Data L H F) : Outcome L H F q := by
    rcases NoISuppliedIdentityConsumer.tract_or_hard L H F D with good|hard
    · exact Or.inl good
    · exact Or.inr (Or.inl hard)
  by_cases live : PaperTerminalBridgeSparseOrders.MiddleLive q
  swap
  · exact Or.inr (Or.inr (Or.inl (PaperTerminalBridgeSparsePure.mapped q even live L.subtype first last)))
  by_cases safe : PaperTerminalBridgeFiniteDeck.NoOneSided (S.family H)
  swap
  · exact completed (PaperTerminalBridgeOneSidedSparseIdentity.produce L H F q label literal even first last live
      (PaperTerminalBridgeDenseSource.oneSided_of_not_safe (S.family H) safe))
  by_cases torsion : ∀t : L,A.Available (S.family H) t→t≠0→IsOfFinOrder t
  · apply Or.inr;apply Or.inr;apply Or.inr
    exact PaperTerminalBridgeSparseFinite.source (S.family H)
      ((algebraicClosure ℚ ℂ).subtype.comp L.subtype) q
      (Gadget.realizes_of_mem _ .disequality _ ⟨label,literal⟩) even first last live zero safe torsion
  · push Not at torsion
    obtain ⟨t,actual,nonzero,infinite⟩:=torsion
    exact completed (PaperTerminalBridgeSparseIdentity.produce L H F
      (PaperTerminalBridgeSparseInfinite.produce H F q label literal even first last live t nonzero actual infinite))

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperTerminalBridgeSparseSource
end
