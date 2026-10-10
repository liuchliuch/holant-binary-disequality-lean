import Holant.Proofs.Dichotomy.Closure.Native.GlobalCloseCompletionNativeMOrdinary
import Holant.Proofs.Dichotomy.Closure.Dense.GlobalCloseCompletionDenseCanonicalCurrent
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeXUniversal
import Holant.Proofs.Dichotomy.Closure.Dense.GlobalCloseCompletionDenseResolved

/-! Native-M continuation with the ordinary obstruction fully discharged.
Dense canonical receipts retain the actual basis and scalar-X graph until
their universal ordinary classification is consumed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionNativeMResolved
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open GlobalCloseCompletionMixedCurrent
open GlobalCloseCompletionNativeMContinuation (CurrentTract)
namespace D
export GlobalCloseCompletionDenseCanonicalCurrent (Outcome fromCurrent)
end D
namespace X
export OrdinaryNegativeXUniversal (classified)
end X
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000
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

abbrev Hard := OrdinaryNegativeFourthCompatibilitySource.Hard G

inductive Completion : Type 1 where
  | hard (proof : Hard G)
  | tract (criterion : CurrentTract G base R)
  | unary (dense : Dense G base R) (singular : StableDenseGaugeCurrent.SingularReceipt G (palette G base R))
      (receipt : StableDenseGaugeUnary.UnaryReceipt G (palette G base R) singular)

def denseContinuation (hd : Dense G base R) :
    D.Outcome G (palette G base R) R.final.ready.torsion N := by
  let o := hd.choose
  let four := hd.choose_spec.choose
  let p := hd.choose_spec.choose_spec.choose
  let full := hd.choose_spec.choose_spec.choose_spec
  exact D.fromCurrent G (palette G base R) R.final.ready.torsion N
    (GeneratedGroupQ4Consumers.table G base four) (GeneratedGroupQ4Consumers.minimum G base four)
    (GeneratedGroupQ4Consumers.minimum_literal G base four) p full

/-- All ordinary and higher-ancestor alternatives are consumed. Only the
singular-unary mathematical branch remains. -/
def complete : Completion G base R := Classical.choice (by
  classical
  by_cases dense : Dense G base R
  · cases denseContinuation G base R N dense with
    | canonical receipt =>
      rcases GlobalCloseCompletionDenseResolved.classified G (palette G base R) receipt.canonical with
        positive | negative
      · exact ⟨.tract positive⟩
      · exact ⟨.hard negative⟩
    | singular r => exact ⟨.unary dense r (StableDenseGaugeUnary.unaryReceipt G (palette G base R) r)⟩
  by_cases tract : EOTract (preprocess
      (GlobalCloseCompletionNativeMContinuation.eoFamily G base R noPrior N))
  · have basis := GlobalCloseCompletionMixedEOSource.common_basis G (palette G base R)
      (row G base R) (models G base R noPrior N) tract
    by_cases covered : ∀o : CurrentOccurrences.Id G (palette G base R),Covered G base R o
    · rcases basis with affine|product
      · exact ⟨.tract (whole_family_of_covered G base R .affine affine covered)⟩
      · exact ⟨.tract (whole_family_of_covered G base R .product product covered)⟩
    · obtain ⟨o,ho⟩ := not_forall.mp covered
      obtain ⟨higher,hh⟩ := (uncovered G base R o ho).resolve_right dense
      have output : Nonempty (GlobalCloseCompletionEq4Graph.Output G (palette G base R)) := by
        rcases basis with affine|product
        · exact ⟨GlobalCloseCompletionEq4Current.output G base R noPrior N .affine affine dense higher hh⟩
        · exact ⟨GlobalCloseCompletionEq4Current.output G base R noPrior N .product product dense higher hh⟩
      obtain ⟨d⟩ := output
      rcases X.classified G (palette G base R) d with positive|negative
      · exact ⟨.tract positive⟩
      · exact ⟨.hard negative⟩
  · refine ⟨.hard ?_⟩
    intro α ea count w
    exact ⟨(GlobalCloseCompletionNativeMContinuation.hardSource G base R noPrior N tract w).reduction⟩)

def ForMarking (M : ClosureMarkedSourceRouting.Marking (ClosureSourceRows.embedding G)
    (palette G base R).family R.final.ready.torsion) : Type 1 :=
  match M with
  | .monomial _native => Completion G base R
  | _ => PUnit.{2}

def forMarking (M : ClosureMarkedSourceRouting.Marking (ClosureSourceRows.embedding G)
    (palette G base R).family R.final.ready.torsion) : ForMarking G base R M := by
  cases M with
  | monomial native => exact complete G base R noPrior native
  | smallTwo => exact PUnit.unit
  | smallFour => exact PUnit.unit
  | cyclic => exact PUnit.unit
  | bilinear => exact PUnit.unit
  | unshifted => exact PUnit.unit
  | shifted => exact PUnit.unit
  | platonic => exact PUnit.unit

def ForResult (result : GeneratedGroupWorklist.Result G base) : Type 1 :=
  match result with
  | .initialStop .. => PUnit.{2}
  | .prepared _ _ (.inl _) => PUnit.{2}
  | .prepared _ _ (.inr exhausted) =>
      ForMarking G base exhausted (ClosureMarkedActualReceipts.produce G
        exhausted.final.source.palette exhausted.final.ready.torsion).physical.marking

def forResult (result : GeneratedGroupWorklist.Result G base) : ForResult G base result :=
  match result with
  | .initialStop .. => PUnit.unit
  | .prepared _ _ (.inl _) => PUnit.unit
  | .prepared _ _ (.inr exhausted) => forMarking G base exhausted rfl _

def original_current_nativeM_resolved : ForResult G (Initial.palette G)
    (GeneratedGroupWorklist.result G (Initial.palette G)) :=
  forResult G (Initial.palette G) (GeneratedGroupWorklist.result G (Initial.palette G))


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionNativeMResolved
end
