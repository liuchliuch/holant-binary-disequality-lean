import Holant.Proofs.Dichotomy.Closure.Stop.GlobalCloseCompletionStopUnarySource
import Holant.Proofs.Dichotomy.Closure.Stop.GlobalCloseCompletionStopOddSource

/-! Every genuine structural stop reaches the same concrete source boundary.
Infinite binaries first use the checked two-unary source; odd rows use the
actual torsion descent or the actual infinite branch. All enlarged palettes
retain the old family, so positive criteria restrict to the exact stopped
current family. Both initial and prepared histories are handled internally. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionStopStructuralSource
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure hiding binarySignature
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.FinitePGL2.Stabilization
namespace U
export GlobalCloseCompletionStopUnarySource (Completion complete)
end U
namespace O
export GlobalCloseCompletionStopOrdinarySource (family family_exact native_family tract_iff_current)
end O
namespace I
export GlobalCloseCompletionStopInfiniteOrdinary
  (field presentation table family toOriginal current_included hasZ
    leftGraph leftLabels leftExact leftOrdinary left_nonzero)
end I
namespace D
export GlobalCloseCompletionStopOddSource (complete)
end D
namespace S
export GlobalCloseCompletionUnaryStructuralSource (unary)
end S
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G):=OI.numberField G
variable (P : Palette G)

variable (B : Binary (K:=OI.K G)) (actual : ActualNonsingular P.family B)
variable (infinite : ¬ProjectivelyFinite (transfer B))

def infiniteFirst : NoXOrdinaryGraphAdjoin.Output (I.table G P B actual infinite) 1 :=
  ⟨I.leftGraph G P B actual infinite,I.leftLabels G P B actual infinite,
    I.leftExact G P B actual infinite,I.leftOrdinary G P B actual infinite⟩

def fromInfinite : U.Completion G P := by
  classical
  letI : Algebra ℚ (I.field G P B actual infinite):=(I.field G P B actual infinite).algebra'
  by_cases tract : Tract (I.family G P B actual infinite)
  · exact .tract ((O.tract_iff_current G P).mp
      (tract.mono_family (I.current_included G P B actual infinite)))
  · exact .source (S.unary G (I.field G P B actual infinite) (I.presentation G P B actual infinite)
      (I.table G P B actual infinite) (I.toOriginal G P B actual infinite)
      (infiniteFirst G P B actual infinite) tract (I.left_nonzero G P B actual infinite)
      (I.hasZ G P B actual infinite))

theorem criterion_restrict (Q : Palette G) (old : P.family⊆Q.family)
    (criterion : TractX (familyAction sourceKBasis (CurrentFrontierClosure.currentFamily G Q))) :
    TractX (familyAction sourceKBasis (CurrentFrontierClosure.currentFamily G P)) := by
  have included : O.family G P⊆O.family G Q := by
    rw [O.family_exact,O.family_exact,O.native_family,O.native_family]
    exact familyAction_mono sourceKBasis (Set.image_mono old)
  exact (O.tract_iff_current G P).mp (((O.tract_iff_current G Q).mpr criterion).mono_family included)

def fromOdd (f : AnySignature (OI.K G)) (retained : f∈P.family) (nonzero : f.2≠0) (odd : Odd f.1) :
    U.Completion G P := by
  cases D.complete G P f retained nonzero odd with
  | unary Q old u retained nonzero source=>
    cases U.complete G Q u retained with
    | tract criterion=>exact .tract (criterion_restrict G P Q old criterion)
    | source result=>exact .source result
  | infinite B actual infinite source=>exact fromInfinite G P B actual infinite

def complete (stop : OccurrenceWorklist.Stop G P) : U.Completion G P :=
  match stop with
  | .unary u retained nonzero=>U.complete G P u retained
  | .infinite B actual infinite=>fromInfinite G P B actual infinite
  | .odd f retained prime large odd=>fromOdd G P f retained prime.1 odd

variable (base : Palette G)
def ForResult (result : GeneratedGroupWorklist.Result G base) : Type 1 :=
  match result with
  | .initialStop ..=>U.Completion G base
  | .prepared _ _ (.inl stopped)=>U.Completion G stopped.finalSource.palette
  | .prepared _ _ (.inr _)=>PUnit.{2}
def forResult (result : GeneratedGroupWorklist.Result G base) : ForResult G base result :=
  match result with
  | .initialStop stop _=>complete G base stop
  | .prepared _ _ (.inl stopped)=>complete G stopped.finalSource.palette stopped.stop
  | .prepared _ _ (.inr _)=>PUnit.unit

def original_structural_sources : ForResult G (Initial.palette G)
    (GeneratedGroupWorklist.result G (Initial.palette G)) :=
  forResult G (Initial.palette G) (GeneratedGroupWorklist.result G (Initial.palette G))


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionStopStructuralSource
end
