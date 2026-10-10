import Holant.Proofs.Dichotomy.Closure.Singular.GlobalCloseCompletionSingularOrdinaryPack
import Holant.Proofs.Dichotomy.Closure.Singular.GlobalCloseCompletionSingularXGraph
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeGenericXUniversal
import Holant.Proofs.Dichotomy.Closure.Eq4.GlobalCloseCompletionEq4Classification

/-! The native-M dense singular branch is fully consumed. The actual dense
slice supplies Eq4, a saved phase supplies a nonzero-off-diagonal traceless
binary, and the saved pin supplies an isotropic full unary. Unequal fourth
powers give an actual even weighted NAND; equal fourth powers give an actual
literal-X adjoin. Both routes use the unchanged original-G oracle. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSingularResolved
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.FinitePGL2.Stabilization
namespace Pr
export GlobalCloseCompletionSingularPrepare (Prepared prepared_exists)
end Pr
namespace S
export GlobalCloseCompletionSingularOrdinaryPack
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
variable (P : Palette G) (d : Pr.Prepared G P)
local instance : Algebra ℚ (S.field G P d) := (S.field G P d).algebra'
local instance : CharZero (S.field G P d) := Algebra.charZero_of_charZero ℚ (S.field G P d)

abbrev CurrentTract := GlobalCloseCompletionEq4Classification.CurrentTract G P
abbrev Hard := OrdinaryNegativeGenericXFourthCompatibilitySource.Hard G

def labels : Fin 2→Fin (S.size G P d) := ![S.h G P d,S.w G P d]

theorem literal : ∀i,(⟨S.arity G P d (labels G P d i).val,S.table G P d (labels G P d i)⟩ :
    AnySignature (S.field G P d))=
      ⟨N.arity i.val,N.table (S.x G P d) (S.y G P d) (S.u G P d) (S.v G P d) i⟩ := by
  intro i
  fin_cases i
  · exact S.hh G P d
  · exact S.hw G P d

include d in
theorem nand_hard (nx : S.x G P d≠0) (fourth : (S.x G P d)^4≠(S.y G P d)^4) : Hard G := by
  intro α ea count w
  let hard := N.source (x:=S.x G P d) (y:=S.y G P d) (u:=S.u G P d) (v:=S.v G P d)
    (square:=S.square G P d) (nx:=nx) (ny:=S.y_nonzero G P d) (nu:=S.u_nonzero G P d)
    (det:=S.nonsingular G P d) (fourth:=fourth)
    (H:=S.table G P d) (labels:=labels G P d) (literal:=literal G P d)
    (F:=S.presentation G P d) (e:=S.e G P d) (p0:=S.p G P d false) (p1:=S.p G P d true)
    (he:=S.he G P d) (h0:=S.hp G P d false) (h1:=S.hp G P d true) w
  exact ⟨(Programme.compose hard (S.toOriginal G P d)).reduction⟩

variable (out : X.Output (S.table G P d))

def data : GenericLiteralXSource.Data G where
  K := S.field G P d
  degree := _
  F := S.presentation G P d
  size := S.size G P d+1
  b := X.arity (S.table G P d) out
  H := X.signatures (S.presentation G P d) (S.table G P d) out
  e := X.old (S.table G P d) (S.e G P d)
  p b := X.old (S.table G P d) (S.p G P d b)
  x := X.xLabel (S.table G P d)
  he := (X.old_literal (S.presentation G P d) (S.table G P d) out _).trans (S.he G P d)
  hp b := (X.old_literal (S.presentation G P d) (S.table G P d) out _).trans (S.hp G P d b)
  hx := X.x_literal (S.presentation G P d) (S.table G P d) out
  toOriginal := Programme.compose (X.source (S.presentation G P d) (S.table G P d) out)
    (S.toOriginal G P d)

theorem transformed_included : familyAction d.anchor.basis (ClosureSourceRows.ambientFamily G d.palette)⊆
    GenericLiteralXSource.family G (data G P d out) := by
  intro f hf
  obtain ⟨i,hi⟩ := S.transformed_included G P d hf
  refine ⟨X.old (S.table G P d) i,?_⟩
  change RingHomRealization.mapAny (S.field G P d).subtype
    (⟨X.arity (S.table G P d) out (X.old (S.table G P d) i).val,
      X.signatures (S.presentation G P d) (S.table G P d) out (X.old (S.table G P d) i)⟩ :
        AnySignature (S.field G P d))=f
  rw [X.old_literal]
  exact hi

private theorem restrict {C : SignatureFamily AlgebraicComplex}
    (hc : CommonKPresentationInKCoordinates C (ClosureSourceRows.ambientFamily G d.palette)) :
    CommonKPresentationInKCoordinates C (ClosureSourceRows.ambientFamily G P) := by
  obtain ⟨_finite,B,edge,rows⟩ := hc
  exact ⟨CurrentFrontierClosure.currentFamily_finite G P,B,edge,fun f hf=>rows f (d.old hf)⟩

theorem tractX_of_tract (tract : Tract (GenericLiteralXSource.family G (data G P d out))) :
    CurrentTract G P := by
  have preprocessed : Preprocessed (ClosureSourceRows.ambientFamily G d.palette) :=
    GlobalCloseCompletionEq4Classification.current_preprocessed G d.palette
  rcases StableHigherCurrentAnchorCommonBasis.native_common_of_ordinary_tract d.anchor
    preprocessed (transformed_included G P d out)
    (GenericLiteralXSource.family_eq4 G (data G P d out)) tract with affine|product|localAffine
  · exact ClosureNativePresentation.tractX_forward_affine (restrict G P d affine)
  · exact ClosureNativePresentation.tractX_forward_product (restrict G P d product)
  · exact ClosureNativePresentation.tractX_forward_localAffine (restrict G P d localAffine)

include out in
theorem x_classified : CurrentTract G P ∨ Hard G := by
  rcases OrdinaryNegativeGenericXUniversal.tract_or_hard G (data G P d out) with tract|hard
  · exact Or.inl (tractX_of_tract G P d out tract)
  · exact Or.inr hard

include d in
/-- Both scalar tests are on the constructed literal field row. No Affine,
hardness, or successful-X premise appears in this terminal. -/
theorem prepared_classified : CurrentTract G P ∨ Hard G := by
  classical
  by_cases zero : S.x G P d=0
  · exact x_classified G P d (XG.directOutput (H:=S.table G P d) (hj:=S.h G P d)
      (x:=S.x G P d) (y:=S.y G P d) (hh:=S.hh G P d) zero (S.y_nonzero G P d))
  by_cases fourth : (S.x G P d)^4=(S.y G P d)^4
  · have same : (S.x G P d)^2=(S.y G P d)^2 := by
      have product : ((S.x G P d)^2-(S.y G P d)^2)*((S.x G P d)^2+(S.y G P d)^2)=0 := by
        linear_combination fourth
      exact sub_eq_zero.mp ((mul_eq_zero.mp product).resolve_right (S.nonsingular G P d))
    exact x_classified G P d (XG.output (H:=S.table G P d) (hj:=S.h G P d)
      (e:=S.e G P d) (uj:=S.w G P d) (x:=S.x G P d) (y:=S.y G P d)
      (u:=S.u G P d) (v:=S.v G P d) (hh:=S.hh G P d) (he:=S.he G P d) (hu:=S.hw G P d)
      (square:=S.square G P d) (same:=same) (nx:=zero) (ny:=S.y_nonzero G P d) (nu:=S.u_nonzero G P d))
  · exact Or.inr (nand_hard G P d zero fourth)

variable (torsion : ResidualTorsion P.family)
variable (N : ClosureMarkedDihedral.NativeM
  (ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G) P.family torsion))
variable (r : StableDenseGaugeCurrent.SingularReceipt G P)
variable (q : Signature (OI.K G) 4) (p : Bool)
variable (full : ∀x,q x≠0 ↔ Holant.Marked.SupportAtlas.parity x=p)
variable (actual : Gadget.Realizes P.family .disequality q)

include torsion N r full actual in
/-- Actual dense native-M singular receipt to whole-original-current
tractability or genuine unchanged-original-G witness-counting hardness. -/
theorem classified : CurrentTract G P ∨ Hard G := by
  obtain ⟨prepared⟩ := Pr.prepared_exists G P torsion N r q p full actual
  exact prepared_classified G P prepared

include torsion N r full actual in
theorem inFP_or_countingHard :
    InFP (OriginalForestSource.inputEncoding (s:=s) (arity:=a))
      (OriginalForestSource.presentation G).encoding (OriginalForestSource.value G) ∨ Hard G := by
  rcases classified G P torsion N r q p full actual with tract|hard
  · exact Or.inl (StablePaletteTractability.original_inFP G P tract)
  · exact Or.inr hard


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSingularResolved
end
