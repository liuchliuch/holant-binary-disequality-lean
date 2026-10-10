import Holant.Proofs.Hardness.EOBinaryPlaneCandidatePositive
import Holant.Proofs.Hardness.EOBinaryPlaneOriginalCommon

/-! Exact coefficient images across original→common→complex embeddings for
the selected candidate and its Gram table. The positive table is derived from
literal coefficient formulas; no real-part homomorphism is used. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneFullSupportImages
open Holant
namespace C
export EOBinaryPlaneCandidateGadgets (output transpose)
end C
namespace N
export EOBinaryPlaneGramGraph (output)
end N
namespace P
export EOBinaryPlanePositive (candidate choice Good exceptional choice_good)
end P
namespace M
export EOBinaryPlaneGramGraphComplex (matrix conjugate)
end M
set_option backward.isDefEq.respectTransparency false

variable {K L : Type} [Field K] [Field L]

theorem candidate_map (into : K→+*L) (f : Signature K 2) (i : Fin 5) :
    (fun z=>into (C.output f i z))=C.output (fun z=>into (f z)) i := by
  funext z
  fin_cases i <;> simp [C.output,C.transpose,EOBinaryPlaneChoiceGadgets.output,map_mul,map_add]

theorem gram_map (into : K→+*L) (f g : Signature K 2) :
    (fun z=>into (N.output f g z))=N.output (fun z=>into (f z)) (fun z=>into (g z)) := by
  funext z
  simp only [N.output,map_sum,map_mul]

theorem matrix_values (f : Signature ℂ 2) :
    M.matrix (f ![false,false]) (f ![false,true]) (f ![true,false]) (f ![true,true])=f := by
  funext z
  have hz : z=![z 0,z 1] := by funext j; fin_cases j <;> rfl
  rw [hz]
  cases z 0 <;> cases z 1 <;> rfl

variable [StarRing L]

def table (into : K→+*L) (f : Signature K 2) (i : Fin 5) : Signature L 2 :=
  N.output (fun z=>into (C.output f i z)) (fun z=>star (into (C.output f i z)))

/-- The common-field Gram output has precisely the real coefficient table
analysed by the finite five-choice producer, with no projective factor. -/
theorem table_image (into : K→+*L) (ambient : L→+*ℂ)
    (hstar : ∀x,ambient (star x)=star (ambient x)) (f : Signature K 2) (i : Fin 5) :
    (fun z=>ambient (table into f i z))=
      fun z=>(P.candidate
        (ambient (into (f ![false,false]))) (ambient (into (f ![false,true])))
        (ambient (into (f ![true,false]))) (ambient (into (f ![true,true]))) i z : ℂ) := by
  rw [table,gram_map]
  simp_rw [hstar]
  change N.output (fun z=>(ambient.comp into) (C.output f i z))
    (M.conjugate (fun z=>(ambient.comp into) (C.output f i z)))=_
  rw [candidate_map]
  let h : Signature ℂ 2 := fun z=>ambient (into (f z))
  have hm := matrix_values h
  have hh := EOBinaryPlaneCandidatePositive.candidate_gram
    (h ![false,false]) (h ![false,true]) (h ![true,false]) (h ![true,true]) i
  rw [hm] at hh
  exact hh

def commonAmbient (M : Signature ℂ 4) : EOBinaryPlaneOriginalCommon.field M→+*ℂ :=
  (EOBinaryPlaneOriginalCommon.field M).subtype

/-- In the internally generated original-M common field, star compatibility
is definitional and is not an extra closure hypothesis on the original field. -/
theorem original_common_star (M : Signature ℂ 4) (x : EOBinaryPlaneOriginalCommon.field M) :
    commonAmbient M (star x)=star (commonAmbient M x) := rfl

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneFullSupportImages
