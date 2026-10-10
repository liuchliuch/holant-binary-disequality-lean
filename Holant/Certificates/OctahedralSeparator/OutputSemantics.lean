import Holant.Certificates.OctahedralSeparator.Outputs
import Holant.Certificates.OctahedralSeparator.ActualResources
import Holant.Certificates.OctahedralSeparator.EndpointChecks
import Holant.Certificates.OctahedralSeparator.BaseRanks
import Holant.Certificates.OctahedralSeparator.RankTransport

namespace Holant.Certificates.OctahedralSeparator
open Holant Holant.Certificates.MatchingProductBridge
noncomputable section

theorem prepared_as_card (j : Fin 48) : prepared j=
    if (rowForm j).val<2 then coefficientCard (rowForm j) (rowBase j)
      else correctedCard (rowForm j) (rowBase j) := by
  rw [prepared_exact]
  unfold preparedLegs
  split <;> rfl

theorem finalLegs_action (j : Fin 48) :
    Signature.coordinateAction (finalLegs j) (coefficientCard (rowForm j) (rowBase j))=
      Signature.coordinateAction (endpointLegs j) (prepared j) := by
  rw [prepared_as_card]
  by_cases h : (rowForm j).val<2
  · have hL : finalLegs j=endpointLegs j := by
      funext a
      simp [finalLegs,h]
    rw [hL,if_pos h]
  · have hL : finalLegs j=(fun a => mm (endpointLegs j a) (corrections (rowForm j) a)) := by
      funext a
      simp [finalLegs,h]
    rw [hL,if_neg h,← corrections_exact,Signature.coordinateAction_comp]
    congr 1
    funext a
    exact (kernel_mul_eq_mm _ _).symm

theorem endpoint_physical (j : Fin 48) (h : ¬outsideRow j) :
    complexTensor (endpointOutput j)=
      Signature.coordinateAction (fun a => complexMatrix (finalLegs j a))
        (complexTensor (coefficientCard (rowForm j) (rowBase j))) := by
  rw [← complexTensor_action,finalLegs_action,endpoint_exact j h]

theorem outside_prepared (j : Fin 48) (h : outsideRow j) :
    prepared j=correctedCard (rowForm j) (rowBase j) := by
  rw [prepared_as_card,if_neg (by have := h.1; omega)]

theorem outside_physical (j : Fin 48) (h : outsideRow j) :
    complexTensor (fun x : Fin 2 → Bool => outsideValues j (x 0) (x 1))=
      Signature.contract (complexMatrix (closureKernel j))
        (Signature.coordinateAction (fun a => complexMatrix (corrections (rowForm j) a))
          (complexTensor (coefficientCard (rowForm j) (rowBase j)))) := by
  rw [outside_exact j h,outside_prepared j h,← corrections_exact,
    complexTensor_contract,complexTensor_action]

theorem prepared_rank_two (j : Fin 48) (h : ¬outsideRow j) (k : Fin 3) :
    (flatten k (complexTensor (prepared j))).rank=2 := by
  let r : Fin 9 := ⟨(rowBase j).val,endpoint_base_regular j h⟩
  have hr : rowBase j=Fin.castAdd 6 r := Fin.ext rfl
  rw [prepared_exact,complexTensor_action,flatten_rank_coordinateAction]
  · rw [hr]
    simpa only [baseCard,Fin.addCases_left] using base_rank_two r k
  · intro a
    rw [← embed_determinant]
    exact embed_ne_zero (prepared_legs_nonsingular _ a)

theorem endpoint_rank_two (j : Fin 48) (h : ¬outsideRow j) (k : Fin 3) :
    (flatten k (complexTensor (endpointOutput j))).rank=2 := by
  rw [endpoint_exact j h,complexTensor_action,flatten_rank_coordinateAction]
  · exact prepared_rank_two j h k
  · intro a
    exact (endpointLegs_available j a).det_ne_zero

end
end Holant.Certificates.OctahedralSeparator
