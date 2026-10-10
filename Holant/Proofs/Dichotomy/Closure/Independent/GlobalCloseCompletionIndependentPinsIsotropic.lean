import Holant.Proofs.Dichotomy.Closure.Independent.GlobalCloseCompletionIndependentPinsNativeSource
import Holant.Proofs.Dichotomy.Closure.Independent.GlobalCloseCompletionIndependentPinsSource
import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryIsotropicLift
import Holant.Proofs.Dichotomy.Closure.Independent.GlobalCloseCompletionIndependentPinsCriterion

/-! The actual isotropic unary and its one-edge Z reflection supply literal
ordinary pins after the exact native-I/ordinary-X wire swap. All intermediate
unary coefficients are retained, and the normalization lives in the actual
native coefficient field. This is an original-G Holant-c source, with no
terminal classification assumed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIndependentPinsIsotropic
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open FixedGadgetSubstitution
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.Hardness.GeneralExtraction.SupportCaps
namespace A
export GlobalCloseCompletionIndependentPinsAdjoin
  (Output signatures arity old newLabel old_literal new_literal source lift)
end A
namespace R
export GlobalCloseCompletionUnaryIsotropicSource (z output reflect_denote)
end R
namespace C
export GlobalCloseCompletionUnaryOrdinaryFieldCodec (ambient)
end C
namespace N
export GlobalCloseCompletionIndependentPinsNativeSource
  (field presentation ordinaryTable arity old xLabel old_literal x_literal scalar scalar_nonzero pin_literal toOriginal mapped_literal)
end N
namespace P
export GlobalCloseCompletionIndependentPinsAlgebra (reflected isotropic_axes)
end P
namespace S
export GlobalCloseCompletionIndependentPinsSource (Data data family old_included)
end S
namespace U
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralOddNonisotropicFrame (norm)
end U
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option maxRecDepth 16384
set_option Elab.async false
variable {r degree : ℕ} {b : ℕ→ℕ}
variable (L : IntermediateField ℚ AlgebraicComplex)
local instance : Algebra ℚ L := L.algebra'
variable (F : FixedField L degree) (H : (i : Fin r)→Signature L (b i.val))
variable (first : A.Output H 1) (nonzero : first.network.denote≠0) (isotropic : U.norm first.network.denote=0)
variable (z : Fin r) (zLiteral : (⟨b z.val,H z⟩ : AnySignature L)=⟨2,R.z⟩)

def reflection : A.Output H 1 :=
  let d:=R.output H first.network first.labels first.exact first.ordinary z zLiteral
  ⟨d.network,d.labels,d.exact,d.ordinary⟩
abbrev firstTable := A.signatures F H first (1:L)
def secondGraph := A.lift F H first (1:L) (reflection L H first z zLiteral)
abbrev originalTable := A.signatures F (firstTable L F H first) (secondGraph L F H first z zLiteral) (1:L)
abbrev originalArity := A.arity (firstTable L F H first) (secondGraph L F H first z zLiteral)
abbrev ambient := C.ambient L (originalTable L F H first z zLiteral)

def oldLabel (i : Fin r) : Fin ((r+1)+1) := A.old (firstTable L F H first) (A.old H i)
def firstLabel : Fin ((r+1)+1) := A.old (firstTable L F H first) (A.newLabel H)
def secondLabel : Fin ((r+1)+1) := A.newLabel (firstTable L F H first)

theorem old_literal (i : Fin r) :
    (⟨originalArity L F H first z zLiteral (oldLabel L F H first i).val,
      originalTable L F H first z zLiteral (oldLabel L F H first i)⟩ : AnySignature L)=⟨b i.val,H i⟩ :=
  (A.old_literal F (firstTable L F H first) (secondGraph L F H first z zLiteral) 1 (A.old H i)).trans
    (A.old_literal F H first 1 i)

theorem first_literal :
    (⟨originalArity L F H first z zLiteral (firstLabel L F H first).val,
      originalTable L F H first z zLiteral (firstLabel L F H first)⟩ : AnySignature L)=⟨1,first.network.denote⟩ := by
  refine (A.old_literal F (firstTable L F H first) (secondGraph L F H first z zLiteral) 1 (A.newLabel H)).trans ?_
  simpa only [div_one] using A.new_literal F H first (1:L)

theorem second_literal :
    (⟨originalArity L F H first z zLiteral (secondLabel L F H first).val,
      originalTable L F H first z zLiteral (secondLabel L F H first)⟩ : AnySignature L)=
      ⟨1,(reflection L H first z zLiteral).network.denote⟩ := by
  simpa only [div_one,secondGraph,A.lift,secondLabel,originalArity,originalTable] using
    A.new_literal F (firstTable L F H first) (secondGraph L F H first z zLiteral) (1:L)

def unary : Signature AlgebraicComplex 1 := fun x=>(first.network.denote x : AlgebraicComplex)

theorem reflected_value : RingHomRealization.mapSignature L.subtype
    (reflection L H first z zLiteral).network.denote=P.reflected (unary L H first) := by
  have h:=R.reflect_denote first.network (Network.corolla (R.z (K:=L))) (Network.denote_corolla _)
  change RingHomRealization.mapSignature L.subtype
    (GlobalCloseCompletionUnaryIsotropicSource.reflect first.network (Network.corolla R.z)).denote=_
  rw [h]
  funext x
  cases h0 : x 0 <;> simp [RingHomRealization.mapSignature,P.reflected,unary,h0]
  all_goals rfl

theorem first_ambient :
    (⟨originalArity L F H first z zLiteral (firstLabel L F H first).val,
      ambient L F H first z zLiteral (firstLabel L F H first)⟩ : AnySignature AlgebraicComplex)=⟨1,unary L H first⟩ :=
  congrArg (RingHomRealization.mapAny L.subtype) (first_literal L F H first z zLiteral)

theorem second_ambient :
    (⟨originalArity L F H first z zLiteral (secondLabel L F H first).val,
      ambient L F H first z zLiteral (secondLabel L F H first)⟩ : AnySignature AlgebraicComplex)=
      ⟨1,P.reflected (unary L H first)⟩ := by
  exact (congrArg (RingHomRealization.mapAny L.subtype) (second_literal L F H first z zLiteral)).trans
    (congrArg (Sigma.mk 1) (reflected_value L H first z zLiteral))

theorem z_ambient :
    (⟨originalArity L F H first z zLiteral (oldLabel L F H first z).val,
      ambient L F H first z zLiteral (oldLabel L F H first z)⟩ : AnySignature AlgebraicComplex)=⟨2,zAnchor⟩ :=
  (congrArg (RingHomRealization.mapAny L.subtype) ((old_literal L F H first z zLiteral z).trans zLiteral)).trans
    (GlobalCloseCompletionUnaryIsotropicLift.z_mapped L)

include nonzero isotropic in
theorem axes : ∃v : Bool,∃c : AlgebraicComplex,c≠0 ∧
    sourceKBasis.symm.action (unary L H first)=purePin c v 1 ∧
    sourceKBasis.symm.action (P.reflected (unary L H first))=purePin c (!v) 1 := by
  apply P.isotropic_axes
  · intro zero
    apply nonzero
    funext x
    exact Subtype.ext (congrFun zero x)
  · change U.norm (fun x=>(first.network.denote x : AlgebraicComplex))=0
    rw [←GlobalCloseCompletionUnaryDescentSource.norm_map L first.network.denote,isotropic]
    rfl

def orientation : Bool := (axes L H first nonzero isotropic).choose
def ambientScale : AlgebraicComplex := (axes L H first nonzero isotropic).choose_spec.choose
theorem axis_data : ambientScale L H first nonzero isotropic≠0 ∧
    sourceKBasis.symm.action (unary L H first)=purePin (ambientScale L H first nonzero isotropic)
      (orientation L H first nonzero isotropic) 1 ∧
    sourceKBasis.symm.action (P.reflected (unary L H first))=purePin (ambientScale L H first nonzero isotropic)
      (!(orientation L H first nonzero isotropic)) 1 :=
  (axes L H first nonzero isotropic).choose_spec.choose_spec

abbrev field := N.field (ambient L F H first z zLiteral)
local instance : Algebra ℚ (field L F H first z zLiteral) := (field L F H first z zLiteral).algebra'
abbrev presentation := N.presentation (ambient L F H first z zLiteral)
abbrev table := N.ordinaryTable (ambient L F H first z zLiteral)

def label (v : Bool) := if v=orientation L H first nonzero isotropic then
    firstLabel L F H first else secondLabel L F H first
def scalar (v : Bool) : field L F H first z zLiteral :=
  N.scalar (ambient L F H first z zLiteral) (label L F H first nonzero isotropic v) v

theorem selected_axis (v : Bool) : ∃u : Signature AlgebraicComplex 1,
    (⟨originalArity L F H first z zLiteral (label L F H first nonzero isotropic v).val,
      ambient L F H first z zLiteral (label L F H first nonzero isotropic v)⟩ : AnySignature AlgebraicComplex)=⟨1,u⟩ ∧
    sourceKBasis.symm.action u=purePin (ambientScale L H first nonzero isotropic) v 1 := by
  classical
  by_cases h : v=orientation L H first nonzero isotropic
  · refine ⟨unary L H first,?_,?_⟩
    · have hl : label L F H first nonzero isotropic v=firstLabel L F H first := by
        unfold label
        exact if_pos h
      rw [hl]
      exact first_ambient L F H first z zLiteral
    · simpa only [h] using (axis_data L H first nonzero isotropic).2.1
  · have hv : v= !(orientation L H first nonzero isotropic) := by
      cases ho : orientation L H first nonzero isotropic <;> cases v <;> simp_all
    refine ⟨P.reflected (unary L H first),?_,?_⟩
    · have hl : label L F H first nonzero isotropic v=secondLabel L F H first := by
        unfold label
        exact if_neg h
      rw [hl]
      exact second_ambient L F H first z zLiteral
    · simpa only [hv] using (axis_data L H first nonzero isotropic).2.2

theorem scalar_nonzero (v : Bool) : scalar L F H first nonzero isotropic z zLiteral v≠0 := by
  obtain ⟨u,literal,axis⟩:=selected_axis L F H first nonzero isotropic z zLiteral v
  exact N.scalar_nonzero (ambient L F H first z zLiteral) _ u literal v _ axis
    (axis_data L H first nonzero isotropic).1

theorem pin_literal (v : Bool) :
    (⟨N.arity (r:=(r+1)+1) (b:=originalArity L F H first z zLiteral)
        (N.old (ambient L F H first z zLiteral) (label L F H first nonzero isotropic v)).val,
      table L F H first z zLiteral (N.old (ambient L F H first z zLiteral) (label L F H first nonzero isotropic v))⟩ :
      AnySignature (field L F H first z zLiteral))=⟨1,purePin (scalar L F H first nonzero isotropic z zLiteral v) v 1⟩ := by
  obtain ⟨u,literal,axis⟩:=selected_axis L F H first nonzero isotropic z zLiteral v
  exact (N.old_literal (ambient L F H first z zLiteral) _).trans
    (N.pin_literal (ambient L F H first z zLiteral) _ u literal v _ axis)

def pins (v : Bool) : A.Output (table L F H first z zLiteral) 1 where
  network := Network.corolla (purePin (scalar L F H first nonzero isotropic z zLiteral v) v 1)
  labels := {
    vertex _ := N.old (ambient L F H first z zLiteral) (label L F H first nonzero isotropic v)
    vertex_arity _ := congrArg Sigma.fst (pin_literal L F H first nonzero isotropic z zLiteral v)
    edge e := Fin.elim0 e }
  exact _ := pin_literal L F H first nonzero isotropic z zLiteral v
  ordinary e := Fin.elim0 e

section Original
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (back : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding r 1 b) F.encoding
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
    ((QuaternaryOrdinaryCompanion.tables F H).evaluate F) (OriginalForestSource.value G))

def literalSource := Programme.compose
  (A.source F (firstTable L F H first) (secondGraph L F H first z zLiteral) (1:L) one_ne_zero)
  (Programme.compose (A.source F H first (1:L) one_ne_zero) back)

def ordinarySource := N.toOriginal G L F (originalTable L F H first z zLiteral)
  (literalSource L F H first z zLiteral G back) (oldLabel L F H first z) (z_ambient L F H first z zLiteral)

def data : S.Data G := S.data G (field L F H first z zLiteral) (presentation L F H first z zLiteral)
  (table L F H first z zLiteral) (ordinarySource L F H first z zLiteral G back)
  (pins L F H first nonzero isotropic z zLiteral) (scalar L F H first nonzero isotropic z zLiteral)
  (scalar_nonzero L F H first nonzero isotropic z zLiteral) (fun v=>Network.denote_corolla _)

theorem intermediate_included :
    GlobalCloseCompletionUnaryDescentSource.ambient (field L F H first z zLiteral) (table L F H first z zLiteral)⊆
      S.family G (data L F H first nonzero isotropic z zLiteral G back) :=
  S.old_included G (field L F H first z zLiteral) (presentation L F H first z zLiteral)
    (table L F H first z zLiteral) (ordinarySource L F H first z zLiteral G back)
    (pins L F H first nonzero isotropic z zLiteral) (scalar L F H first nonzero isotropic z zLiteral)
    (scalar_nonzero L F H first nonzero isotropic z zLiteral) (fun _=>Network.denote_corolla _)

theorem old_transformed :
    familyAction sourceKBasis.symm (GlobalCloseCompletionUnaryDescentSource.ambient L H)⊆
      S.family G (data L F H first nonzero isotropic z zLiteral G back) := by
  rintro f ⟨g,⟨i,rfl⟩,rfl⟩
  apply intermediate_included L F H first nonzero isotropic z zLiteral G back
  refine ⟨N.old (ambient L F H first z zLiteral) (oldLabel L F H first i),?_⟩
  refine (congrArg (RingHomRealization.mapAny (field L F H first z zLiteral).subtype)
    (N.old_literal (ambient L F H first z zLiteral) (oldLabel L F H first i))).trans ?_
  exact N.mapped_literal (ambient L F H first z zLiteral) (oldLabel L F H first i)
    (fun x=>(H i x : AlgebraicComplex))
    (congrArg (RingHomRealization.mapAny L.subtype) (old_literal L F H first z zLiteral i))

theorem hasX : (⟨2,xAnchor⟩ : AnySignature AlgebraicComplex)∈
    S.family G (data L F H first nonzero isotropic z zLiteral G back) := by
  apply intermediate_included L F H first nonzero isotropic z zLiteral G back
  refine ⟨N.xLabel (ambient L F H first z zLiteral),?_⟩
  refine (congrArg (RingHomRealization.mapAny (field L F H first z zLiteral).subtype)
    (N.x_literal (ambient L F H first z zLiteral))).trans ?_
  apply congrArg (fun f : Signature AlgebraicComplex 2=>(⟨2,f⟩ : AnySignature AlgebraicComplex))
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;>
    simp [RingHomRealization.mapSignature,xAnchor,kernelSignature,Signature.disequality,h0,h1]

theorem obstruction (negative : ¬Tract (GlobalCloseCompletionUnaryDescentSource.ambient L H)) :
    ¬Tract (S.family G (data L F H first nonzero isotropic z zLiteral G back)) :=
  GlobalCloseCompletionIndependentPinsCriterion.negative _ _
    (old_transformed L F H first nonzero isotropic z zLiteral G back)
    (hasX L F H first nonzero isotropic z zLiteral G back) negative


end Original
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIndependentPinsIsotropic
end
