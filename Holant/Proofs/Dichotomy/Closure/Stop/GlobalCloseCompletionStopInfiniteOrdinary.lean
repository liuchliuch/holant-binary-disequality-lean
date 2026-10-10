import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryNativeSource
import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryIsotropicLift
import Holant.Proofs.Dichotomy.Closure.Stop.GlobalCloseCompletionStopOrdinarySource
import Holant.Proofs.Dichotomy.Closure.Stop.GlobalCloseCompletionStopInfiniteCurrent

/-! The actual infinite-stop two-unary table enters the ordinary/descent
pipeline directly, with its exact source and coefficient codec. No Palette is
invented for it. Positive whole-family instances return the old original-G
evaluator; both unary norms are tested internally. When both are isotropic,
the retained identity supplies a real reflected independent-unary source. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionStopInfiniteOrdinary
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedGadgetSubstitution
open Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure hiding binarySignature
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace S
export GlobalCloseCompletionStopInfiniteUnary (count arity table family family_exact old_literal left right
  left_literal right_literal left_nonzero right_nonzero toOriginal)
end S
namespace N
export GlobalCloseCompletionUnaryNativeSource (field presentation table family family_exact toOriginal
  graph labels exact ordinary_graph unary unary_nonzero Descent descend)
end N
namespace Old
export GlobalCloseCompletionStopOrdinarySource (family family_exact z_member originalComputes)
end Old
namespace I
export GlobalCloseCompletionUnaryIsotropicLift (output independent toOriginal)
end I
namespace L
export GlobalCloseCompletionUnaryLiteralSource (arity signatures)
end L
namespace U
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralOddNonisotropicFrame (norm)
end U
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 100000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G)
variable (B : Binary (K:=OI.K G)) (actual : ActualNonsingular P.family B)
variable (infinite : ¬ProjectivelyFinite (transfer B))

abbrev native := S.table G P B actual infinite
abbrev field := N.field (native G P B actual infinite)
local instance : Algebra ℚ (field G P B actual infinite) := (field G P B actual infinite).algebra'
abbrev presentation := N.presentation (native G P B actual infinite)
abbrev table := N.table (native G P B actual infinite)
abbrev family := N.family (native G P B actual infinite)
def toOriginal := N.toOriginal (native G P B actual infinite) G (S.toOriginal G P B actual infinite)

theorem current_included : Old.family G P⊆family G P B actual infinite := by
  change Old.family G P⊆N.family (native G P B actual infinite)
  rw [Old.family_exact,N.family_exact]
  apply familyAction_mono sourceKBasis
  rintro f ⟨i,rfl⟩
  exact ⟨⟨i.val,by dsimp only [S.count]; omega⟩,S.old_literal G P B actual infinite i⟩

theorem hasZ : (⟨2,zAnchor⟩ : AnySignature AlgebraicComplex)∈family G P B actual infinite :=
  current_included G P B actual infinite (Old.z_member G P)

def originalComputes (tract : Tract (family G P B actual infinite)) :=
  Old.originalComputes G P (tract.mono_family (current_included G P B actual infinite))

def leftLabel : Fin (S.count G P) := ⟨P.count,by dsimp only [S.count]; omega⟩
def rightLabel : Fin (S.count G P) := ⟨P.count+1,by dsimp only [S.count]; omega⟩
abbrev left : Signature AlgebraicComplex 1 := fun x=>S.left G P B actual infinite (x 0)
abbrev right : Signature AlgebraicComplex 1 := fun x=>S.right G P B actual infinite (x 0)
abbrev leftGraph := N.graph (native G P B actual infinite) (leftLabel G P)
  (left G P B actual infinite) (S.left_literal G P B actual infinite)
abbrev rightGraph := N.graph (native G P B actual infinite) (rightLabel G P)
  (right G P B actual infinite) (S.right_literal G P B actual infinite)
abbrev leftLabels := N.labels (native G P B actual infinite) (leftLabel G P)
  (left G P B actual infinite) (S.left_literal G P B actual infinite)
abbrev leftExact := N.exact (native G P B actual infinite) (leftLabel G P)
  (left G P B actual infinite) (S.left_literal G P B actual infinite)
abbrev leftOrdinary := N.ordinary_graph (native G P B actual infinite) (leftLabel G P)
  (left G P B actual infinite) (S.left_literal G P B actual infinite)

theorem left_nonzero : (leftGraph G P B actual infinite).denote≠0 := by
  rw [leftGraph,N.graph,Network.denote_corolla]
  exact N.unary_nonzero (native G P B actual infinite) (leftLabel G P)
    (left G P B actual infinite) (S.left_literal G P B actual infinite) (S.left_nonzero G P B actual infinite)

abbrev LeftDescent (hu : U.norm (leftGraph G P B actual infinite).denote≠0)
    (negative : ¬Tract (family G P B actual infinite)) :=
  N.Descent (native G P B actual infinite) G (leftLabel G P) (left G P B actual infinite)
    (S.left_literal G P B actual infinite) hu negative
abbrev RightDescent (hu : U.norm (rightGraph G P B actual infinite).denote≠0)
    (negative : ¬Tract (family G P B actual infinite)) :=
  N.Descent (native G P B actual infinite) G (rightLabel G P) (right G P B actual infinite)
    (S.right_literal G P B actual infinite) hu negative

def leftDescent (hu : U.norm (leftGraph G P B actual infinite).denote≠0)
    (negative : ¬Tract (family G P B actual infinite)) : LeftDescent G P B actual infinite hu negative :=
  N.descend (native G P B actual infinite) G (S.toOriginal G P B actual infinite)
    (leftLabel G P) (left G P B actual infinite) (S.left_literal G P B actual infinite) hu negative
def rightDescent (hu : U.norm (rightGraph G P B actual infinite).denote≠0)
    (negative : ¬Tract (family G P B actual infinite)) : RightDescent G P B actual infinite hu negative :=
  N.descend (native G P B actual infinite) G (S.toOriginal G P B actual infinite)
    (rightLabel G P) (right G P B actual infinite) (S.right_literal G P B actual infinite) hu negative

def isotropicOutput := I.output (field G P B actual infinite) (table G P B actual infinite)
  (hasZ G P B actual infinite) (leftGraph G P B actual infinite) (leftLabels G P B actual infinite)
  (leftExact G P B actual infinite) (leftOrdinary G P B actual infinite)

theorem isotropic_independent (isotropic : U.norm (leftGraph G P B actual infinite).denote=0) :
    GlobalCloseCompletionUnaryIsotropicSource.determinant (leftGraph G P B actual infinite).denote
      (isotropicOutput G P B actual infinite).network.denote≠0 :=
  I.independent (field G P B actual infinite) (table G P B actual infinite) (hasZ G P B actual infinite)
    (leftGraph G P B actual infinite) (leftLabels G P B actual infinite)
    (leftExact G P B actual infinite) (leftOrdinary G P B actual infinite)
    (left_nonzero G P B actual infinite) isotropic

abbrev isoArity := L.arity (table G P B actual infinite) (isotropicOutput G P B actual infinite)
abbrev isoTable := L.signatures (presentation G P B actual infinite) (table G P B actual infinite)
  (isotropicOutput G P B actual infinite)
abbrev IsotropicAccess := PhysicalProgramme
  (RawClosedNetwork.validatedEncoding (S.count G P+1) 1 (isoArity G P B actual infinite)) (presentation G P B actual infinite).encoding
  (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
  ((QuaternaryOrdinaryCompanion.tables (presentation G P B actual infinite) (isoTable G P B actual infinite)).evaluate
    (presentation G P B actual infinite)) (OriginalForestSource.value G)

def isotropicSource : IsotropicAccess G P B actual infinite :=
  PhysicalProgramme.ofControlled (I.toOriginal (field G P B actual infinite) (table G P B actual infinite)
    (hasZ G P B actual infinite) (leftGraph G P B actual infinite) (leftLabels G P B actual infinite)
    (leftExact G P B actual infinite) (leftOrdinary G P B actual infinite)
    (presentation G P B actual infinite) G (toOriginal G P B actual infinite))

inductive Completion : Type 1 where
  | tract (criterion : Tract (family G P B actual infinite))
      (evaluator : Computes (OriginalForestSource.inputEncoding (s:=s) (arity:=a))
        (OriginalForestSource.presentation G).encoding (OriginalForestSource.value G))
  | left (negative : ¬Tract (family G P B actual infinite))
      (nonisotropic : U.norm (leftGraph G P B actual infinite).denote≠0)
      (descent : LeftDescent G P B actual infinite nonisotropic negative)
  | right (negative : ¬Tract (family G P B actual infinite))
      (left_isotropic : U.norm (leftGraph G P B actual infinite).denote=0)
      (nonisotropic : U.norm (rightGraph G P B actual infinite).denote≠0)
      (descent : RightDescent G P B actual infinite nonisotropic negative)
  | isotropic (negative : ¬Tract (family G P B actual infinite))
      (left_zero : U.norm (leftGraph G P B actual infinite).denote=0)
      (right_zero : U.norm (rightGraph G P B actual infinite).denote=0)
      (independent : GlobalCloseCompletionUnaryIsotropicSource.determinant
        (leftGraph G P B actual infinite).denote (isotropicOutput G P B actual infinite).network.denote≠0)
      (source : IsotropicAccess G P B actual infinite)

def complete : Completion G P B actual infinite := by
  classical
  by_cases tract : Tract (family G P B actual infinite)
  · exact .tract tract (originalComputes G P B actual infinite tract)
  by_cases hl : U.norm (leftGraph G P B actual infinite).denote=0
  · by_cases hr : U.norm (rightGraph G P B actual infinite).denote=0
    · exact .isotropic tract hl hr (isotropic_independent G P B actual infinite hl)
        (isotropicSource G P B actual infinite)
    · exact .right tract hl hr (rightDescent G P B actual infinite hr tract)
  · exact .left tract hl (leftDescent G P B actual infinite hl tract)

def ForStop (stop : OccurrenceWorklist.Stop G P) : Type 1 :=
  match stop with
  | .infinite B actual infinite=>Completion G P B actual infinite
  | .unary ..=>PUnit.{2}
  | .odd ..=>PUnit.{2}
def forStop (stop : OccurrenceWorklist.Stop G P) : ForStop G P stop :=
  match stop with
  | .infinite B actual infinite=>complete G P B actual infinite
  | .unary ..=>PUnit.unit
  | .odd ..=>PUnit.unit

variable (base : Palette G)
def ForResult (result : GeneratedGroupWorklist.Result G base) : Type 1 :=
  match result with
  | .initialStop stop _=>ForStop G base stop
  | .prepared _ _ (.inl stopped)=>ForStop G stopped.finalSource.palette stopped.stop
  | .prepared _ _ (.inr _)=>PUnit.{2}
def forResult (result : GeneratedGroupWorklist.Result G base) : ForResult G base result :=
  match result with
  | .initialStop stop _=>forStop G base stop
  | .prepared _ _ (.inl stopped)=>forStop G stopped.finalSource.palette stopped.stop
  | .prepared _ _ (.inr _)=>PUnit.unit
def original_infinite_ordinary : ForResult G (Initial.palette G)
    (GeneratedGroupWorklist.result G (Initial.palette G)) :=
  forResult G (Initial.palette G) (GeneratedGroupWorklist.result G (Initial.palette G))


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionStopInfiniteOrdinary
end
