import Holant.Proofs.Hardness.GeneratedSignatureField
import Holant.Proofs.Hardness.ComplexConeStageAccess

/-! Original input data and actual finite cone entry for arbitrary complex
selfdual dense EO. The output tensor stays in the original generated field;
its separate ambient presentation is handled only by an actual answer map. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.ComplexSelfdualData
open Holant Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.Hardness.EightVertexNonexception
namespace O
export Holant.LocalDrafts.Hardness.EightVertexNonexception.Source
  (field fieldSignature fieldSignature_eq_zero fieldSignature_value presentation TargetInput targetEncoding targetValue target_value_exact)
end O
namespace S
export ThreeModeSignatures (original eo)
end S
namespace V
export RealDenseSignTwistStageAccess (value signatures kernels)
end V
namespace C
export ComplexConeEntry (data outputA outputB outputC AllNZ Cone)
end C
namespace F
export GeneratedSignatureField (ambient algebraic source)
end F
set_option backward.isDefEq.respectTransparency false

structure Applicable {K : Type} [Field K] (M : Signature K 4) : Prop where
  eo : DenseEOUnitLocal.EOSupport M
  oppositeA : (entries M).b=(entries M).y
  oppositeB : (entries M).d=(entries M).w
  oppositeC : (entries M).c=(entries M).z
  nonzeroA : (entries M).b≠0
  nonzeroB : (entries M).d≠0
  nonzeroC : (entries M).c≠0

theorem reconstruct {K : Type} [Field K] (M : Signature K 4) (h : Applicable M) :
    M=S.original (entries M).b (entries M).d (entries M).c := by
  have hz := DenseEOUnitLocal.corners_zero M h.eo
  have ht : entries M=⟨0,(entries M).b,(entries M).c,(entries M).d,
      (entries M).d,(entries M).c,(entries M).b,0⟩ := by
    ext <;> simp only [hz.1,hz.2,←h.oppositeA,←h.oppositeB,←h.oppositeC]
  rw [←table_entries M (DenseEOUnitLocal.even M h.eo),ht]
  rfl

variable (M : Signature ℂ 4) (h : Applicable M)
local instance originalAlgebra : Algebra ℚ (O.field M) := (O.field M).algebra'
def alpha : O.field M := (entries (O.fieldSignature M)).b
def beta : O.field M := (entries (O.fieldSignature M)).d
def gamma : O.field M := (entries (O.fieldSignature M)).c

include h in
theorem field_applicable : Applicable (O.fieldSignature M) where
  eo := DenseEOPairedSource.field_eo M h.eo
  oppositeA := Subtype.ext h.oppositeA
  oppositeB := Subtype.ext h.oppositeB
  oppositeC := Subtype.ext h.oppositeC
  nonzeroA := fun hz=>h.nonzeroA ((O.fieldSignature_eq_zero M _).mp hz)
  nonzeroB := fun hz=>h.nonzeroB ((O.fieldSignature_eq_zero M _).mp hz)
  nonzeroC := fun hz=>h.nonzeroC ((O.fieldSignature_eq_zero M _).mp hz)

include h in
theorem field_signature : O.fieldSignature M=S.original (alpha M) (beta M) (gamma M) :=
  reconstruct _ (field_applicable M h)

def selected := C.data (entries M).b (entries M).d (entries M).c
  ⟨h.nonzeroA,h.nonzeroB,h.nonzeroC⟩

def generated : Signature (O.field M) 4 :=
  ComplexConeStageAccess.normalized (alpha M) (beta M) (gamma M)
    (selected M h).step (selected M h).choice

def output : Signature ℂ 4 := F.ambient M (generated M h)

theorem output_eq : output M h=
    S.original (C.outputA (entries M).b (entries M).d (entries M).c (selected M h).step (selected M h).choice)
      (C.outputB (entries M).b (entries M).d (entries M).c (selected M h).step (selected M h).choice)
      (C.outputC (entries M).b (entries M).d (entries M).c (selected M h).step (selected M h).choice) := by
  have ha : ((C.outputA (alpha M) (beta M) (gamma M) (selected M h).step (selected M h).choice : O.field M) : ℂ)=
      C.outputA (entries M).b (entries M).d (entries M).c (selected M h).step (selected M h).choice := by
    generalize (selected M h).step=t
    generalize (selected M h).choice=i
    cases t <;> fin_cases i <;> rfl
  have hb : ((C.outputB (alpha M) (beta M) (gamma M) (selected M h).step (selected M h).choice : O.field M) : ℂ)=
      C.outputB (entries M).b (entries M).d (entries M).c (selected M h).step (selected M h).choice := by
    generalize (selected M h).step=t
    generalize (selected M h).choice=i
    cases t <;> fin_cases i <;> rfl
  have hc : ((C.outputC (alpha M) (beta M) (gamma M) (selected M h).step (selected M h).choice : O.field M) : ℂ)=
      C.outputC (entries M).b (entries M).d (entries M).c (selected M h).step (selected M h).choice := by
    generalize (selected M h).step=t
    generalize (selected M h).choice=i
    cases t <;> fin_cases i <;> rfl
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp only [output,F.ambient,generated,ComplexConeStageAccess.normalized,S.original,table,h0,h1,h2,h3]
  all_goals first | exact ha | exact hb | exact hc | rfl

theorem output_applicable : Applicable (output M h) := by
  rw [output_eq]
  exact ⟨S.eo _ _ _,rfl,rfl,rfl,(selected M h).allNZ.1,
    (selected M h).allNZ.2.1,(selected M h).allNZ.2.2⟩

theorem output_cone : C.Cone (entries (output M h)).b (entries (output M h)).d
    (entries (output M h)).c := by
  rw [output_eq]
  exact (selected M h).cone

variable (halg : ∀x,IsAlgebraic ℚ (M x))
theorem target_value (r : O.TargetInput) : V.value (O.fieldSignature M) r=O.targetValue M halg r := by
  apply Subtype.ext
  rw [O.target_value_exact]
  change ((O.field M).subtype ((r.val.realize r.property (V.signatures (O.fieldSignature M))
    V.kernels).denote Fin.elim0))=_
  rw [←Network.denote_map (O.field M).subtype]
  apply congrFun (Network.denote_congr (r.val.shape r.property) _ _ _ _ ?_ ?_) Fin.elim0
  · intro v x; exact O.fieldSignature_value M x
  · intro e x y; cases x <;> cases y <;> rfl

def stageSource : LengthControlledOracleReduction O.targetEncoding (O.presentation M halg).encoding
    O.targetEncoding (O.presentation M halg).encoding (V.value (generated M h)) (O.targetValue M halg) := by
  have r := ComplexConeStageAccess.source (O.presentation M halg) (alpha M) (beta M) (gamma M)
    (selected M h).step (selected M h).choice
  have ht : V.value (S.original (alpha M) (beta M) (gamma M))=O.targetValue M halg := by
    rw [←field_signature M h]
    exact funext (target_value M halg)
  rw [ht] at r
  exact r

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.ComplexSelfdualData
