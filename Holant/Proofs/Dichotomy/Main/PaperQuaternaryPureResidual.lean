import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOriginalInput
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIQuaternaryPureReduction

/-! Exact original-input boundary for the third theorem. The single remaining
pure Eq4 source class is explicit, so this is not a completed dichotomy. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryPureResidual
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.Hardness.EightVertexNonexception
namespace I
export NoIOriginalInput (field presentation table source lift ambient)
end I
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : Algebra ℚ (I.field G):=(I.field G).algebra'
variable (q : Signature AlgebraicComplex 4) (label : Fin s)
variable (literal : (⟨a label.val,G label⟩ : AnySignature AlgebraicComplex)=⟨4,q⟩)
variable (even : EvenSupport q) (first : (entries q).a≠0) (last : (entries q).x≠0)

abbrev Criterion:=Tract (familyAction sourceKBasis (PaperLiteralEqualityCriterion.family G))
def Outcome : Prop := Criterion G ∨ (PaperLiteralEqualityHardness.target G).Hard ∨
    Nonempty (NoISparseComplementComplete.PureData (I.field G) (I.table G) (I.presentation G))

include literal even first last in
theorem source : Outcome G := by
  obtain ⟨f,retained,mapped⟩:=I.lift G q label literal
  have fe : EvenSupport f := by
    intro x odd
    apply (I.field G).subtype.injective
    have h:=congrFun mapped x
    change (I.field G).subtype (f x)=q x at h
    exact h.trans ((even x odd).trans (map_zero _).symm)
  have ff : (entries f).a≠0 := by
    intro zero
    apply first
    have h:=congrFun mapped ![false,false,false,false]
    change (I.field G).subtype ((entries f).a)=(entries q).a at h
    rw [zero,map_zero] at h
    exact h.symm
  have fl : (entries f).x≠0 := by
    intro zero
    apply last
    have h:=congrFun mapped ![true,true,true,true]
    change (I.field G).subtype ((entries f).x)=(entries q).x at h
    rw [zero,map_zero] at h
    exact h.symm
  rcases NoIQuaternaryPureReduction.source (I.field G) (I.table G) (I.presentation G)
      f label retained fe ff fl with good|hard|pure
  · exact Or.inl (by simpa only [I.ambient] using good)
  · exact Or.inr (Or.inl (NoIOrdinaryRaw.Target.Hard.compose
      (S:=NoISuppliedIdentityConsumer.target (I.field G) (I.table G) (I.presentation G))
      (T:=PaperLiteralEqualityHardness.target G) hard (I.source G)))
  · exact Or.inr (Or.inr pure)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryPureResidual
end
