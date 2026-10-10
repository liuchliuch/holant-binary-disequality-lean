import Holant.Proofs.Dichotomy.Main.PaperControlledOrdinary
import Holant.Proofs.Dichotomy.Closure.B.GlobalCloseCompletionBUnary
import Holant.Proofs.Dichotomy.Main.PaperControlled.BCurrent
import Holant.Proofs.Dichotomy.Main.PaperControlled.BDenseResolved
import Holant.Proofs.Dichotomy.General.GenericLiteralXBSource

/-! Every higher, sparse, ordinary and canonical dense B branch is consumed.
The only residual is an actual original-field singular binary backed by a
selected dense normalized q4 and an actual saved full-support, nonisotropic
unary, with graph, coefficient and access preserved. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlled.BResolved
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace B
export PaperControlled.BCurrent (palette Dense small_tract complete)
end B
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (base : Palette G)
variable {A : GeneratedGroupWorklist.Active G base}
variable (R : GeneratedGroupWorklist.Exhausted G base A) (noPrior : A.source.done=∅)
variable (N : ClosureMarkedDihedralB.NativeB
  (ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G)
    (B.palette G base R).family R.final.ready.torsion))
abbrev Hard := PaperControlledHardness.Original G
abbrev CurrentTract := GlobalCloseCompletionEq4Classification.CurrentTract G (B.palette G base R)

inductive Completion : Type 1 where
  | hard (proof : Hard G)
  | tract (criterion : CurrentTract G base R)
  | singular (dense : B.Dense G base R)
      (receipt : GlobalCloseCompletionBDenseEscape.SingularReceipt G (B.palette G base R))
      (unary : GlobalCloseCompletionBUnary.UnaryReceipt G (B.palette G base R) receipt)

include N in
theorem denseContinuation (dense : B.Dense G base R) :
    CurrentTract G base R ∨ Hard G ∨
      Nonempty (GlobalCloseCompletionBDenseEscape.SingularReceipt G (B.palette G base R)) := by
  obtain ⟨o,four,p,full⟩ := dense
  exact PaperControlled.BDenseResolved.fullParity_classified G (B.palette G base R)
    R.final.ready.torsion N (GeneratedGroupQ4Consumers.table G base four)
    (GeneratedGroupQ4Consumers.minimum G base four)
    (GeneratedGroupQ4Consumers.minimum_literal G base four) p full

def complete : Completion G base R := Classical.choice (by
  cases B.complete G base R noPrior N with
  | hard proof => exact ⟨.hard proof⟩
  | tract criterion => exact ⟨.tract criterion⟩
  | ordinary output obstruction =>
      exact ⟨.hard (PaperControlledOrdinary.literalX_countingHard G
        (GenericLiteralXBSource.source G (B.palette G base R) output) obstruction)⟩
  | dense full =>
      rcases denseContinuation G base R N full with tract|hard|singular
      · exact ⟨.tract tract⟩
      · exact ⟨.hard hard⟩
      · obtain ⟨r⟩ := singular
        exact ⟨.singular full r (GlobalCloseCompletionBUnary.unaryReceipt G (B.palette G base R) r)⟩)

def ForMarking (M : ClosureMarkedSourceRouting.Marking (ClosureSourceRows.embedding G)
    (B.palette G base R).family R.final.ready.torsion) : Type 1 := match M with
  | .bilinear _ => Completion G base R
  | _ => PUnit.{2}

def forMarking (M : ClosureMarkedSourceRouting.Marking (ClosureSourceRows.embedding G)
    (B.palette G base R).family R.final.ready.torsion) : ForMarking G base R M := by
  cases M with
  | bilinear native => exact complete G base R noPrior native
  | smallTwo => exact PUnit.unit
  | smallFour => exact PUnit.unit
  | cyclic => exact PUnit.unit
  | monomial => exact PUnit.unit
  | unshifted => exact PUnit.unit
  | shifted => exact PUnit.unit
  | platonic => exact PUnit.unit

def ForResult (result : GeneratedGroupWorklist.Result G base) : Type 1 := match result with
  | .initialStop .. => PUnit.{2}
  | .prepared _ _ (.inl _) => PUnit.{2}
  | .prepared _ _ (.inr exhausted) =>
      ForMarking G base exhausted (ClosureMarkedActualReceipts.produce G
        exhausted.final.source.palette exhausted.final.ready.torsion).physical.marking

def forResult (result : GeneratedGroupWorklist.Result G base) : ForResult G base result := match result with
  | .initialStop .. => PUnit.unit
  | .prepared _ _ (.inl _) => PUnit.unit
  | .prepared _ _ (.inr exhausted) => forMarking G base exhausted rfl _

def original_current_bilinear_resolved : ForResult G (Initial.palette G)
    (GeneratedGroupWorklist.result G (Initial.palette G)) :=
  forResult G (Initial.palette G) (GeneratedGroupWorklist.result G (Initial.palette G))


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlled.BResolved
end
