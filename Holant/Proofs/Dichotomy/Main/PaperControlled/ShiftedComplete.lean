import Holant.Proofs.Dichotomy.Main.PaperControlledHardness
import Holant.Proofs.Dichotomy.Closure.Shifted.GlobalCloseCompletionShiftedOrdinaryCurrent
import Holant.Proofs.Dichotomy.Main.PaperControlled.ShiftedAllAntiTerminal
import Holant.Tractable.Downward

/-! Complete actual exhausted shifted marking. The order-four LocalAffine
arm is consumed by its original-field weighted-antidiagonal source. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlled.ShiftedComplete
open Computability Holant Holant.Tractable Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace D
export GlobalCloseCompletionShiftedDescent (Native)
end D
namespace Q
export GeneratedGroupQ4Consumers (table minimum minimum_literal matching)
end Q
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (base : Palette G)
variable {A : GeneratedGroupWorklist.Active G base}
variable (R : GeneratedGroupWorklist.Exhausted G base A) (noPrior : A.source.done=∅)
abbrev palette := R.final.source.palette
variable (native : D.Native G (palette G base R) R.final.ready.torsion)
abbrev CurrentTract := TractX (familyAction sourceKBasis (CurrentFrontierClosure.currentFamily G (palette G base R)))
abbrev Hard := PaperControlledHardness.Original G

private theorem tract_mono {F H : SignatureFamily AlgebraicComplex}
    (h : TractX F) (sub : H⊆F) : TractX H := by
  have hp := preprocess_mono sub
  refine ⟨h.1.subset hp,?_⟩
  rcases h.2 with small|affine|product|localAffine
  · exact Or.inl (small.mono_family hp)
  · exact Or.inr (Or.inl (affine.mono_family hp))
  · exact Or.inr (Or.inr (Or.inl (product.mono_family hp)))
  · exact Or.inr (Or.inr (Or.inr (localAffine.mono_family hp)))

include noPrior native in
theorem classified : CurrentTract G base R ∨ Hard G := by
  cases GlobalCloseCompletionShiftedOrdinaryCurrent.complete G base R noPrior native with
  | tract criterion => exact Or.inl criterion
  | ordinary parent higher descent obstruction =>
    let q := Q.table G base descent.four
    let core := Q.minimum G base descent.four
    have literal : core.signature=⟨4,q⟩ := Q.minimum_literal G base descent.four
    have stable := Q.matching G base (R.preparationReceipt G base noPrior descent.endpoint) descent.four
    rcases PaperControlled.ShiftedAllAntiTerminal.classified G (palette G base R)
      R.final.ready.torsion native q core literal stable with positive|negative
    · refine Or.inl (tract_mono positive ?_)
      apply familyAction_mono sourceKBasis
      exact Set.image_mono (GlobalCloseCompletionShiftedExplicitAnchor.old_included G
        (palette G base R) R.final.ready.torsion q core literal)
    · exact Or.inr negative

include noPrior native in
theorem inFP_or_countingHard :
    InFP (OriginalForestSource.inputEncoding (s:=s) (arity:=a))
      (OriginalForestSource.presentation G).encoding (OriginalForestSource.value G) ∨ Hard G := by
  rcases classified G base R noPrior native with tract|hard
  · exact Or.inl (StablePaletteTractability.original_inFP G (palette G base R) tract)
  · exact Or.inr hard

def ForMarking (M : ClosureMarkedSourceRouting.Marking (ClosureSourceRows.embedding G)
    (palette G base R).family R.final.ready.torsion) : Prop := match M with
  | .shifted .. => CurrentTract G base R ∨ Hard G
  | _ => True

include noPrior in
theorem forMarking (M : ClosureMarkedSourceRouting.Marking (ClosureSourceRows.embedding G)
    (palette G base R).family R.final.ready.torsion) : ForMarking G base R M := by
  cases M with
  | shifted axis noncyclic notTwo notFour noZ reflection sameSource =>
      exact classified G base R noPrior ⟨axis,noncyclic,notTwo,notFour,noZ,reflection,sameSource⟩
  | smallTwo => trivial
  | smallFour => trivial
  | cyclic => trivial
  | monomial => trivial
  | bilinear => trivial
  | unshifted => trivial
  | platonic => trivial

def ForResult (result : GeneratedGroupWorklist.Result G base) : Prop := match result with
  | .initialStop .. => True
  | .prepared _ _ (.inl _) => True
  | .prepared _ _ (.inr exhausted) =>
      ForMarking G base exhausted (ClosureMarkedActualReceipts.produce G
        exhausted.final.source.palette exhausted.final.ready.torsion).physical.marking

theorem forResult (result : GeneratedGroupWorklist.Result G base) : ForResult G base result :=
  match result with
  | .initialStop .. => trivial
  | .prepared _ _ (.inl _) => trivial
  | .prepared _ _ (.inr exhausted) => forMarking G base exhausted rfl _

theorem original_current_shifted_complete : ForResult G (Initial.palette G)
    (GeneratedGroupWorklist.result G (Initial.palette G)) :=
  forResult G (Initial.palette G) (GeneratedGroupWorklist.result G (Initial.palette G))


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlled.ShiftedComplete
end
