import Holant.Proofs.Dichotomy.Closure.Mixed.GlobalCloseCompletionMixedCurrent

/-! Actual original-G mixed low-arity closure. The completed binary/sparse-q4
branch reconstructs the entire retained factor forest and installs the real
native evaluator. The only nonterminal native-M alternatives explicitly retain
a genuine higher ancestor or a dense q4; global Close is not asserted here. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionMixedRoot
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.Hardness.FrozenFactorNormalization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open GlobalCloseCompletionMixedCurrent
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (base : Palette G)
variable {A : GeneratedGroupWorklist.Active G base}
variable (R : GeneratedGroupWorklist.Exhausted G base A) (noPrior : A.source.done=∅)
variable (N : ClosureMarkedDihedral.NativeM
  (ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G)
    (palette G base R).family R.final.ready.torsion))

abbrev OriginalFP : Prop := InFP (OriginalForestSource.inputEncoding (s:=s) (arity:=a))
  (OriginalForestSource.presentation G).encoding (OriginalForestSource.value G)

def evaluator (tract : TractX (familyAction sourceKBasis
    (CurrentFrontierClosure.currentFamily G (palette G base R)))) :=
  StablePaletteTractability.originalComputes G (palette G base R) tract

def ComputationalOutcome : Prop := GlobalCloseCompletionMixedEOSource.OriginalHard G ∨
  OriginalFP G ∨ Higher G base R ∨ Dense G base R

include noPrior N in
/-- The tractable branch contains the actual original-G evaluator; the caller
supplies no oracle implementation, answer codec identification or time bound. -/
theorem computational_outcome : ComputationalOutcome G base R := by
  rcases outcome G base R noPrior N with hard|tract|higher|dense
  · exact Or.inl hard
  · exact Or.inr (Or.inl (StablePaletteTractability.original_inFP G (palette G base R) tract))
  · exact Or.inr (Or.inr (Or.inl higher))
  · exact Or.inr (Or.inr (Or.inr dense))

def ForMarking (M : ClosureMarkedSourceRouting.Marking (ClosureSourceRows.embedding G)
    (palette G base R).family R.final.ready.torsion) : Prop :=
  match M with
  | .monomial _ => Outcome G base R ∧ ComputationalOutcome G base R
  | _ => True

include noPrior in
theorem forMarking (M : ClosureMarkedSourceRouting.Marking (ClosureSourceRows.embedding G)
    (palette G base R).family R.final.ready.torsion) : ForMarking G base R M := by
  cases M with
  | monomial N => exact ⟨outcome G base R noPrior N,computational_outcome G base R noPrior N⟩
  | smallTwo => trivial
  | smallFour => trivial
  | cyclic => trivial
  | bilinear => trivial
  | unshifted => trivial
  | shifted => trivial
  | platonic => trivial

def ForResult (result : GeneratedGroupWorklist.Result G base) : Prop :=
  match result with
  | .initialStop .. => True
  | .prepared _ _ (.inl _) => True
  | .prepared _ _ (.inr exhausted) =>
      ForMarking G base exhausted (ClosureMarkedActualReceipts.produce G
        exhausted.final.source.palette exhausted.final.ready.torsion).physical.marking

theorem forResult (result : GeneratedGroupWorklist.Result G base) : ForResult G base result := by
  cases result with
  | initialStop => trivial
  | prepared ready recomputed completion =>
      cases completion with
      | inl => trivial
      | inr exhausted => exact forMarking G base exhausted rfl _

/-- Unconditional same-execution producer. All local hypotheses of the mixed
binary/sparse closure, including exact preparation, are discharged internally. -/
theorem original_current_mixed_outcome : ForResult G (Initial.palette G)
    (GeneratedGroupWorklist.result G (Initial.palette G)) :=
  forResult G (Initial.palette G) (GeneratedGroupWorklist.result G (Initial.palette G))


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionMixedRoot
end
