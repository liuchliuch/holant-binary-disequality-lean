import Holant.Proofs.Hardness.ThreeModeGraphEvaluation
import Holant.Proofs.Hardness.DenseEOPairedSource
import Holant.Proofs.Hardness.ComplexDynamicParameters

/-! Complex norm-cone self-dual data on the original signature.
The oracle answers remain in exactly its coefficient-generated field. The
canonical complex inclusion is used only to prove finite-size separation. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.ComplexDynamicOriginalData
open Holant Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.Hardness.EightVertexNonexception
namespace O
export Holant.LocalDrafts.Hardness.EightVertexNonexception.Source
  (field fieldSignature fieldSignature_value fieldSignature_eq_zero presentation
   TargetInput targetEncoding targetValue target_value_exact)
end O
namespace S
export ThreeModeSignatures (original)
end S
namespace G
export ThreeModeGraphEvaluation (targetValue targetSignatures kernels)
end G
set_option backward.isDefEq.respectTransparency false

/-- Explicit genuinely complex norm-cone branch in the original coefficients. -/
structure Applicable (M : Signature ℂ 4) : Prop where
  eo : DenseEOUnitLocal.EOSupport M
  oppositeA : (entries M).b=(entries M).y
  oppositeB : (entries M).d=(entries M).w
  oppositeC : (entries M).c=(entries M).z
  nonzeroA : (entries M).b≠0
  nonzeroB : (entries M).d≠0
  nonzeroC : (entries M).c≠0
  nonzeroSum : (entries M).b+(entries M).d≠0
  normRatio : ‖(entries M).c/((entries M).b+(entries M).d)‖<1
  normOddRatio : ‖((entries M).d-(entries M).b)*((entries M).b+(entries M).d)‖/‖(entries M).c‖^2<1

variable (M : Signature ℂ 4)

theorem reconstruct (h : Applicable M) :
    M=S.original (entries M).b (entries M).d (entries M).c := by
  have hz := DenseEOUnitLocal.corners_zero M h.eo
  have ht : entries M=⟨0,(entries M).b,(entries M).c,(entries M).d,
      (entries M).d,(entries M).c,(entries M).b,0⟩ := by
    ext <;> simp only [hz.1,hz.2,←h.oppositeA,←h.oppositeB,←h.oppositeC]
  rw [←table_entries M (DenseEOUnitLocal.even M h.eo),ht]
  rfl

local instance fieldAlgebra : Algebra ℚ (O.field M) := (O.field M).algebra'
local instance fieldCharZero : CharZero (O.field M) := algebraRat.charZero (O.field M)

def alpha : O.field M := (entries (O.fieldSignature M)).b
def beta : O.field M := (entries (O.fieldSignature M)).d
def gamma : O.field M := (entries (O.fieldSignature M)).c

def parameters (h : Applicable M) : ComplexDynamicParameters.Data where
  a := (entries M).b
  b := (entries M).d
  c := (entries M).c
  a_ne := h.nonzeroA
  b_ne := h.nonzeroB
  c_ne := h.nonzeroC
  mu_ne := h.nonzeroSum
  ratio_lt := h.normRatio
  oddRatio_lt := h.normOddRatio

theorem alpha_value (h : Applicable M) : (O.field M).subtype (alpha M)=(parameters M h).a := rfl
theorem beta_value (h : Applicable M) : (O.field M).subtype (beta M)=(parameters M h).b := rfl
theorem gamma_value (h : Applicable M) : (O.field M).subtype (gamma M)=(parameters M h).c := rfl

theorem field_signature (h : Applicable M) :
    O.fieldSignature M=S.original (alpha M) (beta M) (gamma M) := by
  have heo := DenseEOPairedSource.field_eo M h.eo
  have hz := DenseEOUnitLocal.corners_zero (O.fieldSignature M) heo
  have ha : (entries (O.fieldSignature M)).b=(entries (O.fieldSignature M)).y :=
    Subtype.ext h.oppositeA
  have hb : (entries (O.fieldSignature M)).d=(entries (O.fieldSignature M)).w :=
    Subtype.ext h.oppositeB
  have hc : (entries (O.fieldSignature M)).c=(entries (O.fieldSignature M)).z :=
    Subtype.ext h.oppositeC
  have ht : entries (O.fieldSignature M)=⟨0,alpha M,gamma M,beta M,beta M,gamma M,alpha M,0⟩ := by
    ext <;> simp only [alpha,beta,gamma,hz.1,hz.2,←ha,←hb,←hc]
  rw [←table_entries (O.fieldSignature M) (DenseEOUnitLocal.even (O.fieldSignature M) heo),ht]
  rfl

theorem alpha_nonzero (h : Applicable M) : alpha M≠0 := by
  intro hz
  have he := congrArg (O.field M).subtype hz
  exact h.nonzeroA he

theorem beta_nonzero (h : Applicable M) : beta M≠0 := by
  intro hz
  have he := congrArg (O.field M).subtype hz
  exact h.nonzeroB he

theorem gamma_nonzero (h : Applicable M) : gamma M≠0 := by
  intro hz
  have he := congrArg (O.field M).subtype hz
  exact h.nonzeroC he

variable (halg : ∀x,IsAlgebraic ℚ (M x)) (h : Applicable M)

include h in
theorem target_value (r : O.TargetInput) :
    G.targetValue (alpha M) (beta M) (gamma M) r=O.targetValue M halg r := by
  apply Subtype.ext
  rw [O.target_value_exact]
  change ((O.field M).subtype
    ((r.val.realize r.property (G.targetSignatures (alpha M) (beta M) (gamma M))
      G.kernels).denote Fin.elim0))=_
  rw [←Network.denote_map (O.field M).subtype]
  apply congrFun (Network.denote_congr (r.val.shape r.property) _ _ _ _ ?_ ?_) Fin.elim0
  · intro v x
    change ((S.original (alpha M) (beta M) (gamma M) x : O.field M) : ℂ)=M x
    rw [←field_signature M h]
    exact O.fieldSignature_value M x
  · intro e x y
    cases x <;> cases y <;> rfl

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.ComplexDynamicOriginalData
