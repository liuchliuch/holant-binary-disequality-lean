import Holant.Proofs.Hardness.ThreeModeGraphEvaluation
import Holant.Proofs.Hardness.DenseEOPairedSource

/-! Explicit original-M conditions and its internally generated coefficient
field. The ambient norm is inherited by that subfield; no extension field or
chosen embedding is an additional input. Answer bytes remain the existing
original-field presentation, rather than an ambient-field codec. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.ThreeModeOriginalData
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
variable {L : Type} [NormedField L] [Algebra ℚ L]

/-- A stated spectral-dominance subcase of self-dual dense EO, not all dense EO. -/
structure Applicable (M : Signature L 4) : Prop where
  eo : DenseEOUnitLocal.EOSupport M
  oppositeA : (entries M).b=(entries M).y
  oppositeB : (entries M).d=(entries M).w
  oppositeC : (entries M).c=(entries M).z
  nonzeroA : (entries M).b≠0
  nonzeroB : (entries M).d≠0
  nonzeroC : (entries M).c≠0
  dominantPlus : ‖(entries M).b+(entries M).d‖<‖(entries M).c‖
  dominantMinus : ‖(entries M).d-(entries M).b‖<‖(entries M).c‖

variable (M : Signature L 4)

omit [Algebra ℚ L] in
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

theorem field_applicable (h : Applicable M) : Applicable (O.fieldSignature M) where
  eo := DenseEOPairedSource.field_eo M h.eo
  oppositeA := Subtype.ext h.oppositeA
  oppositeB := Subtype.ext h.oppositeB
  oppositeC := Subtype.ext h.oppositeC
  nonzeroA := fun hz=>h.nonzeroA ((O.fieldSignature_eq_zero M _).mp hz)
  nonzeroB := fun hz=>h.nonzeroB ((O.fieldSignature_eq_zero M _).mp hz)
  nonzeroC := fun hz=>h.nonzeroC ((O.fieldSignature_eq_zero M _).mp hz)
  dominantPlus := h.dominantPlus
  dominantMinus := h.dominantMinus

theorem field_signature (h : Applicable M) :
    O.fieldSignature M=S.original (alpha M) (beta M) (gamma M) :=
  reconstruct (O.fieldSignature M) (field_applicable M h)

theorem alpha_nonzero (h : Applicable M) : alpha M≠0 := (field_applicable M h).nonzeroA
theorem beta_nonzero (h : Applicable M) : beta M≠0 := (field_applicable M h).nonzeroB
theorem gamma_nonzero (h : Applicable M) : gamma M≠0 := (field_applicable M h).nonzeroC

theorem field_dominantPlus (h : Applicable M) : ‖alpha M+beta M‖<‖gamma M‖ :=
  (field_applicable M h).dominantPlus

theorem field_dominantMinus (h : Applicable M) : ‖beta M-alpha M‖<‖gamma M‖ :=
  (field_applicable M h).dominantMinus

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
    change ((S.original (alpha M) (beta M) (gamma M) x : O.field M) : L)=M x
    rw [←field_signature M h]
    exact O.fieldSignature_value M x
  · intro e x y
    cases x <;> cases y <;> rfl

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.ThreeModeOriginalData
