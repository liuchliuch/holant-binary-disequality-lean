import Holant.Proofs.Dichotomy.Main.PaperControlledHardness
import Holant.Proofs.Dichotomy.Main.PaperControlled.KleinEq4Source
import Holant.Proofs.Dichotomy.Retained.StableDenseGaugeCurrent

/-! An actual projective Eq4 realization over the same current alphabet is
normalized to a labelled ordinary graph and consumed by the real joint source.
No source capability or tractability promise is supplied separately. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlled.KleinRealizedEq4
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity FixedGadgetSubstitution
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G)
variable (actual : Gadget.RealizesUpTo (ClosureSourceRows.ambientFamily G P) .disequality
  (Holant.EightVertex.ProductAnchor.equalityFour (K:=AlgebraicComplex)))

include actual in
theorem output : Nonempty (GlobalCloseCompletionBPrimeEq4.Output
    (PaperControlled.KleinEq4Source.mapped G P)) := by
  obtain ⟨c,hc,actual⟩ := actual
  obtain ⟨N,uses,native,denote⟩ := Holant.OpenNetworkComposition.OrdinaryNormalization.realizes_exists_ordinary
    (StableDenseGaugeCurrent.ambient_identity G P) actual
  have finiteUses : ∀v,∃j : Fin P.count,
      (⟨P.arity j.val,PaperControlled.KleinEq4Source.mapped G P j⟩ : AnySignature AlgebraicComplex)=
        ⟨N.shape.arity v,N.vertex v⟩ := by
    intro v
    obtain ⟨g,⟨j,rfl⟩,literal⟩ := uses v
    exact ⟨j,literal⟩
  let labels : Labelling N.shape P.count 1 P.arity :=
    { vertex := fun v=>(finiteUses v).choose
      vertex_arity := fun v=>congrArg Sigma.fst (finiteUses v).choose_spec
      edge := fun _=>0 }
  exact ⟨⟨N,labels,fun v=>(finiteUses v).choose_spec,native,c,hc,denote⟩⟩

include actual in
theorem classified : PaperControlled.KleinEq4Source.CurrentTract G P ∨
    PaperControlled.KleinEq4Source.Hard G := by
  obtain ⟨d⟩ := output G P actual
  exact PaperControlled.KleinEq4Source.classified G P d

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlled.KleinRealizedEq4
end
