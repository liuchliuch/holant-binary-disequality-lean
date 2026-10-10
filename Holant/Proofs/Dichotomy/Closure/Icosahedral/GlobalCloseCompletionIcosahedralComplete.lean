import Holant.Proofs.Dichotomy.Closure.Icosahedral.GlobalCloseCompletionIcosahedralStableCurrent
import Holant.Proofs.Closure.FrontierSmallArity
import Holant.Proofs.Dichotomy.Retained.StablePaletteTractability

/-! Complete actual exhausted semantic-I marking. Every prepared minimum
contradicts its own literal raw deck, so the exact final-palette scan returns
the implemented small-family tractability source in the unchanged basis. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIcosahedralComplete
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
abbrev CurrentTract := TractX (familyAction sourceKBasis
  (CurrentFrontierClosure.currentFamily G (palette G base R)))

include noPrior in
theorem classified
    (semantic : HasModel (overgroup (ClosureSourceRows.embedding G)
      (palette G base R).family R.final.ready.torsion) (.platonic .icosahedral)) :
    CurrentTract G base R := by
  cases FrontierSmallArity.inspect G (palette G base R) with
  | small empty tract => exact tract
  | large data =>
    let core := data.minimum G
    obtain ⟨m,f,proper,even,literal,stable⟩ := GroupPreparedStability.forExhausted G base R noPrior core
    exact False.elim (GlobalCloseCompletionIcosahedral.StableCurrent.semantic_current_impossible
      G (palette G base R) R.final.ready.torsion f proper even core literal stable semantic)

include noPrior in
theorem inFP
    (semantic : HasModel (overgroup (ClosureSourceRows.embedding G)
      (palette G base R).family R.final.ready.torsion) (.platonic .icosahedral)) :
    InFP (OriginalForestSource.inputEncoding (s:=s) (arity:=a))
      (OriginalForestSource.presentation G).encoding (OriginalForestSource.value G) :=
  StablePaletteTractability.original_inFP G (palette G base R)
    (classified G base R noPrior semantic)

def ForMarking (M : ClosureMarkedSourceRouting.Marking (ClosureSourceRows.embedding G)
    (palette G base R).family R.final.ready.torsion) : Prop := match M with
  | .platonic .icosahedral _ => CurrentTract G base R
  | _ => True

include noPrior in
theorem forMarking (M : ClosureMarkedSourceRouting.Marking (ClosureSourceRows.embedding G)
    (palette G base R).family R.final.ready.torsion) : ForMarking G base R M := by
  cases M with
  | platonic p model =>
      cases p with
      | icosahedral => exact classified G base R noPrior model
      | tetrahedral => trivial
      | octahedral => trivial
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

theorem original_current_icosahedral_complete : ForResult G (Initial.palette G)
    (GeneratedGroupWorklist.result G (Initial.palette G)) :=
  forResult G (Initial.palette G) (GeneratedGroupWorklist.result G (Initial.palette G))


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIcosahedralComplete
end
