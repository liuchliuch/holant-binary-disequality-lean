import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralQ4
import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralHigherCurrent
import Holant.Proofs.Dichotomy.Retained.StablePaletteTractability
import Holant.Proofs.Closure.FrontierSmallArity

/-! Complete actual exhausted semantic-O marking, at every arity. The real
final-palette scan supplies either small-family tractability or its own
minimum. Every minimum above four contradicts the original stable deck;
the actual q4 endpoint supplies whole-current tractability or original-G
counting hardness. No caller classification or successful source is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralComplete
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
abbrev Hard := OrdinaryNegativeGenericXFourthCompatibilitySource.Hard G

include noPrior in
theorem classified
    (semantic : HasModel (overgroup (ClosureSourceRows.embedding G)
      (palette G base R).family R.final.ready.torsion) (.platonic .octahedral)) :
    CurrentTract G base R ∨ Hard G := by
  cases FrontierSmallArity.inspect G (palette G base R) with
  | small empty tract => exact Or.inl tract
  | large data =>
    let core := data.minimum G
    obtain ⟨m,f,proper,even,literal,stable⟩ := GroupPreparedStability.forExhausted G base R noPrior core
    have hp : Prime (⟨m+2,f⟩ : AnySignature (OI.K G)) := literal ▸ core.prime
    by_cases four : m=2
    · subst m
      exact GlobalCloseCompletionOctahedralQ4.current_classified G (palette G base R)
        R.final.ready.torsion f core literal stable semantic
    · have high : 6≤m+2 := by
        obtain ⟨k,hk⟩ := even
        omega
      exact False.elim (GlobalCloseCompletionOctahedralHigherCurrent.semantic_prime_impossible
        (ClosureSourceRows.embedding G) (palette G base R).family R.final.ready.torsion
        f stable (palette G base R).equality semantic high hp)

include noPrior in
theorem inFP_or_countingHard
    (semantic : HasModel (overgroup (ClosureSourceRows.embedding G)
      (palette G base R).family R.final.ready.torsion) (.platonic .octahedral)) :
    InFP (OriginalForestSource.inputEncoding (s:=s) (arity:=a))
      (OriginalForestSource.presentation G).encoding (OriginalForestSource.value G) ∨ Hard G := by
  rcases classified G base R noPrior semantic with tract|hard
  · exact Or.inl (StablePaletteTractability.original_inFP G (palette G base R) tract)
  · exact Or.inr hard

def ForMarking (M : ClosureMarkedSourceRouting.Marking (ClosureSourceRows.embedding G)
    (palette G base R).family R.final.ready.torsion) : Prop := match M with
  | .platonic .octahedral _ => CurrentTract G base R ∨ Hard G
  | _ => True

include noPrior in
theorem forMarking (M : ClosureMarkedSourceRouting.Marking (ClosureSourceRows.embedding G)
    (palette G base R).family R.final.ready.torsion) : ForMarking G base R M := by
  cases M with
  | platonic p model =>
      cases p with
      | octahedral => exact classified G base R noPrior model
      | tetrahedral => trivial
      | icosahedral => trivial
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

theorem original_current_octahedral_complete : ForResult G (Initial.palette G)
    (GeneratedGroupWorklist.result G (Initial.palette G)) :=
  forResult G (Initial.palette G) (GeneratedGroupWorklist.result G (Initial.palette G))


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralComplete
end
