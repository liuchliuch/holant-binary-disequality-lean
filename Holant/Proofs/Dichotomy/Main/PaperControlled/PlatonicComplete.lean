import Holant.Proofs.Dichotomy.Main.PaperControlledHardness
import Holant.Proofs.Dichotomy.Closure.Tetrahedral.GlobalCloseCompletionTetrahedralComplete
import Holant.Proofs.Dichotomy.Main.PaperControlled.OctahedralComplete
import Holant.Proofs.Dichotomy.Closure.Icosahedral.GlobalCloseCompletionIcosahedralComplete

/-! All three semantic platonic models are consumed on the exact same
exhausted original-palette source. The criterion has one common basis for
the entire current family, or an unchanged-original-G counting programme. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlled.PlatonicComplete
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.Projective.BoundedTorsion Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.FinitePGL2 Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open ClosureMarkedReversalOvergroup.Ambient
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (base : Palette G)
variable {A : GeneratedGroupWorklist.Active G base}
variable (R : GeneratedGroupWorklist.Exhausted G base A) (noPrior : A.source.done=∅)
abbrev palette := R.final.source.palette
abbrev CurrentTract := GlobalCloseCompletionEq4Classification.CurrentTract G (palette G base R)
abbrev Hard := PaperControlledHardness.Original G

include noPrior in
theorem classified (model : Holant.Certificates.MatchingProductBridge.PlatonicModel)
    (semantic : HasModel (overgroup (ClosureSourceRows.embedding G)
      (palette G base R).family R.final.ready.torsion) (.platonic model)) :
    CurrentTract G base R ∨ Hard G := by
  cases model with
  | tetrahedral => exact Or.inl (GlobalCloseCompletionTetrahedralComplete.classified G base R noPrior semantic)
  | octahedral => exact PaperControlled.OctahedralComplete.classified G base R noPrior semantic
  | icosahedral => exact Or.inl (GlobalCloseCompletionIcosahedralComplete.classified G base R noPrior semantic)

include noPrior in
theorem inFP_or_countingHard (model : Holant.Certificates.MatchingProductBridge.PlatonicModel)
    (semantic : HasModel (overgroup (ClosureSourceRows.embedding G)
      (palette G base R).family R.final.ready.torsion) (.platonic model)) :
    InFP (OriginalForestSource.inputEncoding (s:=s) (arity:=a))
      (OriginalForestSource.presentation G).encoding (OriginalForestSource.value G) ∨ Hard G := by
  rcases classified G base R noPrior model semantic with tract|hard
  · exact Or.inl (StablePaletteTractability.original_inFP G (palette G base R) tract)
  · exact Or.inr hard

def ForMarking (M : ClosureMarkedSourceRouting.Marking (ClosureSourceRows.embedding G)
    (palette G base R).family R.final.ready.torsion) : Prop := match M with
  | .platonic _ _ => CurrentTract G base R ∨ Hard G
  | _ => True

include noPrior in
theorem forMarking (M : ClosureMarkedSourceRouting.Marking (ClosureSourceRows.embedding G)
    (palette G base R).family R.final.ready.torsion) : ForMarking G base R M := by
  cases M with
  | platonic p model => exact classified G base R noPrior p model
  | smallTwo => trivial
  | smallFour => trivial
  | cyclic => trivial
  | monomial => trivial
  | bilinear => trivial
  | unshifted => trivial
  | shifted => trivial

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

theorem original_current_platonic_complete : ForResult G (Initial.palette G)
    (GeneratedGroupWorklist.result G (Initial.palette G)) :=
  forResult G (Initial.palette G) (GeneratedGroupWorklist.result G (Initial.palette G))


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlled.PlatonicComplete
end
