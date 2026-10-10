import Holant.Proofs.Dichotomy.Closure.Generic.GlobalCloseCompletionGenericSingularPack
import Holant.Proofs.Dichotomy.Closure.Singular.GlobalCloseCompletionSingularXGraph
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeGenericXUniversal
import Holant.Proofs.Dichotomy.Closure.Eq4.GlobalCloseCompletionEq4Classification

/-! The native-M dense singular branch is fully consumed. The actual dense
slice supplies Eq4, a saved phase supplies a nonzero-off-diagonal traceless
binary, and the saved pin supplies an isotropic full unary. Unequal fourth
powers give an actual even weighted NAND; equal fourth powers give an actual
literal-X adjoin. Both routes use the unchanged original-G oracle. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionGenericSingularResolved
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.FinitePGL2.Stabilization
namespace S
export GlobalCloseCompletionGenericSingularPack
  (field presentation size arity table e p h w x y u v he hp hh hw
   y_nonzero nonsingular u_nonzero square toOriginal family transformed_included)
end S
namespace X
export GlobalCloseCompletionOrdinaryXAdjoin (Output arity signatures old xLabel old_literal x_literal source)
end X
namespace XG
export GlobalCloseCompletionSingularXGraph (output directOutput)
end XG
namespace N
export GlobalCloseCompletionSingularNAND (arity table source)
end N
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 32768
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (d : GlobalCloseCompletionGenericSingularPack.Input G)
local instance : Algebra ℚ (S.field G d) := (S.field G d).algebra'
local instance : CharZero (S.field G d) := Algebra.charZero_of_charZero ℚ (S.field G d)

abbrev nativeFamily := UniversalPairReduction.FiniteFamily.family d.table
abbrev Positive :=
  CommonKPresentationInKCoordinates affineClass (nativeFamily G d) ∨
    CommonKPresentationInKCoordinates productClass (nativeFamily G d) ∨
    CommonKPresentationInKCoordinates localAffineClass (nativeFamily G d)
abbrev Hard := OrdinaryNegativeGenericXFourthCompatibilitySource.Hard G

def labels : Fin 2→Fin (S.size G d) := ![S.h G d,S.w G d]

theorem literal : ∀i,(⟨S.arity G d (labels G d i).val,S.table G d (labels G d i)⟩ :
    AnySignature (S.field G d))=
      ⟨N.arity i.val,N.table (S.x G d) (S.y G d) (S.u G d) (S.v G d) i⟩ := by
  intro i
  fin_cases i
  · exact S.hh G d
  · exact S.hw G d

include d in
theorem nand_hard (nx : S.x G d≠0) (fourth : (S.x G d)^4≠(S.y G d)^4) : Hard G := by
  intro α ea count w
  let hard := N.source (x:=S.x G d) (y:=S.y G d) (u:=S.u G d) (v:=S.v G d)
    (square:=S.square G d) (nx:=nx) (ny:=S.y_nonzero G d) (nu:=S.u_nonzero G d)
    (det:=S.nonsingular G d) (fourth:=fourth)
    (H:=S.table G d) (labels:=labels G d) (literal:=literal G d)
    (F:=S.presentation G d) (e:=S.e G d) (p0:=S.p G d false) (p1:=S.p G d true)
    (he:=S.he G d) (h0:=S.hp G d false) (h1:=S.hp G d true) w
  exact ⟨(Programme.compose hard (S.toOriginal G d)).reduction⟩

variable (out : X.Output (S.table G d))

def data : GenericLiteralXSource.Data G where
  K := S.field G d
  degree := _
  F := S.presentation G d
  size := S.size G d+1
  b := X.arity (S.table G d) out
  H := X.signatures (S.presentation G d) (S.table G d) out
  e := X.old (S.table G d) (S.e G d)
  p b := X.old (S.table G d) (S.p G d b)
  x := X.xLabel (S.table G d)
  he := (X.old_literal (S.presentation G d) (S.table G d) out _).trans (S.he G d)
  hp b := (X.old_literal (S.presentation G d) (S.table G d) out _).trans (S.hp G d b)
  hx := X.x_literal (S.presentation G d) (S.table G d) out
  toOriginal := Programme.compose (X.source (S.presentation G d) (S.table G d) out)
    (S.toOriginal G d)

theorem transformed_included : familyAction d.anchor.basis (nativeFamily G d)⊆
    GenericLiteralXSource.family G (data G d out) := by
  intro f hf
  obtain ⟨i,hi⟩ := S.transformed_included G d hf
  refine ⟨X.old (S.table G d) i,?_⟩
  change RingHomRealization.mapAny (S.field G d).subtype
    (⟨X.arity (S.table G d) out (X.old (S.table G d) i).val,
      X.signatures (S.presentation G d) (S.table G d) out (X.old (S.table G d) i)⟩ :
        AnySignature (S.field G d))=f
  rw [X.old_literal]
  exact hi

variable (preprocessed : Preprocessed (nativeFamily G d))

include preprocessed in
theorem positive_of_tract (tract : Tract (GenericLiteralXSource.family G (data G d out))) :
    Positive G d :=
  StableHigherCurrentAnchorCommonBasis.native_common_of_ordinary_tract d.anchor
    preprocessed (transformed_included G d out)
    (GenericLiteralXSource.family_eq4 G (data G d out)) tract

include out preprocessed in
theorem x_classified : Positive G d ∨ Hard G := by
  rcases OrdinaryNegativeGenericXUniversal.tract_or_hard G (data G d out) with tract|hard
  · exact Or.inl (positive_of_tract G d out preprocessed tract)
  · exact Or.inr hard

include d preprocessed in
/-- Both scalar tests are on the constructed literal field row. No Affine,
hardness, or successful-X premise appears in this terminal. -/
theorem classified : Positive G d ∨ Hard G := by
  classical
  by_cases zero : S.x G d=0
  · exact x_classified G d (XG.directOutput (H:=S.table G d) (hj:=S.h G d)
      (x:=S.x G d) (y:=S.y G d) (hh:=S.hh G d) zero (S.y_nonzero G d)) preprocessed
  by_cases fourth : (S.x G d)^4=(S.y G d)^4
  · have same : (S.x G d)^2=(S.y G d)^2 := by
      have product : ((S.x G d)^2-(S.y G d)^2)*((S.x G d)^2+(S.y G d)^2)=0 := by
        linear_combination fourth
      exact sub_eq_zero.mp ((mul_eq_zero.mp product).resolve_right (S.nonsingular G d))
    exact x_classified G d (XG.output (H:=S.table G d) (hj:=S.h G d)
      (e:=S.e G d) (uj:=S.w G d) (x:=S.x G d) (y:=S.y G d)
      (u:=S.u G d) (v:=S.v G d) (hh:=S.hh G d) (he:=S.he G d) (hu:=S.hw G d)
      (square:=S.square G d) (same:=same) (nx:=zero) (ny:=S.y_nonzero G d) (nu:=S.u_nonzero G d)) preprocessed
  · exact Or.inr (nand_hard G d zero fourth)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionGenericSingularResolved
end
