import Holant.Certificates.OctahedralSeparator.ExitData
import Holant.Certificates.OctahedralSeparator.EndpointChecks
import Holant.Certificates.OctahedralSeparator.PrintedEndpoints
import Holant.Certificates.OctahedralSeparator.TensorSemantics
import Holant.Certificates.OctahedralSeparator.GroupMembership
import Holant.Certificates.TetrahedralOrientation.Resources

namespace Holant.Certificates.OctahedralSeparator
open Holant
noncomputable section
set_option maxHeartbeats 1000000

theorem endpoint_eightVertex (j : Fin 48) (h : ¬outsideRow j) :
    TetrahedralOrientation.EndpointNondegenerateEightVertex (complexTensor (endpointOutput j)) := by
  obtain ⟨ho,h0,h1⟩ := endpoint_coefficients j h
  refine ⟨?_,embed_ne_zero h0,embed_ne_zero h1⟩
  intro x hx
  change embed (endpointOutput j x)=0
  rw [ho x hx,embed_zero]

theorem endpoint_printed_exact (j : Fin 48) (h : ¬outsideRow j) :
    complexTensor (endpointOutput j)=embed (endpointScale j) • complexTensor (printedEndpoint j) := by
  rw [printed_endpoints_exact j h]
  exact complexTensor_scale _ _

def complexEq4 : Signature ℂ 4 := fun x => if x=(fun _ => false) ∨ x=(fun _ => true) then 1 else 0

theorem equality_output : complexTensor (endpointOutput 34)=
    embed (coeff (3/8) (1/4) 0 0) • complexEq4 := by
  rw [equality_exact]
  funext x
  simp only [complexTensor,tensorScale,embed_mul,Pi.smul_apply,smul_eq_mul]
  congr 1
  unfold eq4 complexEq4
  split <;> simp [embed_zero,embed_one]

theorem equality_output_scale_nonzero : embed (coeff (3/8) (1/4) 0 0) ≠ 0 :=
  embed_ne_zero equality_scale_nonzero

theorem outside_nonsingular (j : Fin 48) (h : outsideRow j) :
    Matrix.det (complexMatrix (outsideValues j)) ≠ 0 := by
  rw [← embed_determinant,outside_determinant j h]
  exact embed_ne_zero (outside_det_nonzero j h)

theorem outside_not_direction (j : Fin 48) (h : outsideRow j) :
    ¬ Direction (rowForm j) (complexMatrix (mm (outsideValues j) flip)) := by
  rintro ⟨c,hc,k,heq⟩
  have hpull : embed (outsideScale j) • complexMatrix (directionMatrix j)=
      c • complexMatrix (standard k) := by
    calc
      _ = complexPull (rowForm j) (complexMatrix (mm (outsideValues j) flip)) := by
        rw [← complexMatrix_pull,outside_direction j h,complexMatrix_ms]
      _ = _ := by
        rw [heq,complexPull_smul,complexMatrix_theta,complexPull_complexTheta]
  obtain ⟨a,b,d,e,hne⟩ := outside_different j h k
  have h1 := congrFun (congrFun hpull a) b
  have h2 := congrFun (congrFun hpull d) e
  change embed (outsideScale j)*embed (directionMatrix j a b)=c*embed (standard k a b) at h1
  change embed (outsideScale j)*embed (directionMatrix j d e)=c*embed (standard k d e) at h2
  apply hne
  apply embed_injective
  rw [embed_mul,embed_mul]
  apply mul_left_cancel₀ (embed_ne_zero (outside_scale_nonzero j h))
  calc
    _ = (embed (outsideScale j)*embed (directionMatrix j a b))*embed (standard k d e) := by ring
    _ = (embed (outsideScale j)*embed (directionMatrix j d e))*embed (standard k a b) := by
      rw [h1,h2]
      ring
    _ = _ := by ring

theorem embedded_nativeTransfer (U : Mat) :
    nativeTransfer (complexMatrix U)=complexMatrix (mm U flip) := by
  rw [complexMatrix_mm,complexMatrix_flip]
  rfl

theorem outside_transfer_not_direction (j : Fin 48) (h : outsideRow j) :
    ¬ Direction (rowForm j) (nativeTransfer (complexMatrix (outsideValues j))) := by
  rw [embedded_nativeTransfer]
  exact outside_not_direction j h

end
end Holant.Certificates.OctahedralSeparator
