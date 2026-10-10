import Holant.Certificates.PlatonicQuaternaryExits.Native
import Holant.Certificates.TetrahedralOrientation.Interface
import Holant.Certificates.OctahedralSeparator.Interface
import Holant.Certificates.IcosahedralSeparator.Interface

/-! The complete regular part of A.26, with the original q rather than its
six-port ancestor as the unique nonbinary resource. All 3+96+60 indexed source
outputs have a literal native-X graph of the required size. -/
namespace Holant.Certificates.PlatonicQuaternaryExits
open Holant Holant.Certificates.MatchingProductBridge
open Holant.Certificates.OctahedralSeparator (nativeTransfer)
open Holant.Certificates.OctahedralSeparator.Native (binarySignature pairVertex legVertex)
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem nativeTransfer_eq_multiply (U : Kernel ℂ) : nativeTransfer U=multiply U X := by
  ext a b
  cases b <;> simp [nativeTransfer,Kernel.mul_disequality,multiply,X,Signature.disequality]

/-- The second alternative is a nonzero scalar equality, hence in particular
a pure generalized equality on exactly the two constant four-bit words. -/
def Exit (D : Direction) (q : Signature ℂ 4) : Prop :=
  (∃ t : Signature ℂ 4, BoundedRealization D q t ∧
    TetrahedralOrientation.EndpointNondegenerateEightVertex t ∧
    ∀ r : Fin 3, (flatten r t).rank=2) ∨
  (∃ c : ℂ, c≠0 ∧ BoundedRealization D q (c • OctahedralSeparator.complexEq4)) ∨
  ∃ B : Kernel ℂ, BoundedRealization D q (binarySignature B) ∧
    Matrix.det (Matrix.of B)≠0 ∧ ¬D (nativeTransfer B)

theorem tetrahedral_reverse (s : TetrahedralOrientation.Orientation) :
    Exit (fun U => groupDirection .tetrahedral U) (TetrahedralOrientation.card s) := by
  refine Or.inl ⟨TetrahedralOrientation.dressed s,?_,
    TetrahedralOrientation.dressed_eightVertex s,TetrahedralOrientation.dressed_rank_two s⟩
  apply Native.dressed_bounded
  intro j
  rw [OctahedralSeparator.nativeTransfer_legVertex]
  exact TetrahedralOrientation.legs_direction s j

namespace Octahedral
open Holant.Certificates.OctahedralSeparator

def output (f : Form) (frame : Fin 4) (order : Fin 6) : Signature ℂ 4 :=
  complexTensor (coefficientCard f (Fin.castAdd 6 (frames frame (permutations order 0))))

theorem endpoint_bounded (j : Fin 48) (h : ¬outsideRow j) :
    BoundedRealization (OctahedralSeparator.Direction (rowForm j))
      (complexTensor (coefficientCard (rowForm j) (rowBase j))) (complexTensor (endpointOutput j)) := by
  rw [endpoint_physical j h]
  apply PlatonicQuaternaryExits.Native.dressed_bounded
  intro a
  exact legVertex_available (finalLegs_available j a)

theorem outside_bounded (j : Fin 48) (h : outsideRow j) :
    BoundedRealization (OctahedralSeparator.Direction (rowForm j))
      (complexTensor (coefficientCard (rowForm j) (rowBase j)))
      (binarySignature (complexMatrix (outsideValues j))) := by
  have hc : (fun a => complexMatrix (corrections (rowForm j) a))=
      ![Signature.equality,complexMatrix (correction (rowForm j)),
        Signature.equality,complexMatrix (correction (rowForm j))] := by
    funext a
    fin_cases a <;> simp [corrections,quaternionBasis,Q0] <;> rfl
  change BoundedRealization _ _ (complexTensor (fun x : Fin 2 → Bool => outsideValues j (x 0) (x 1)))
  rw [outside_physical j h,hc]
  have hn := PlatonicQuaternaryExits.Native.sparse_bounded (OctahedralSeparator.Direction (rowForm j)) (Equiv.refl _)
    (complexTensor (coefficientCard (rowForm j) (rowBase j)))
    (complexMatrix (correction (rowForm j))) (complexMatrix (correction (rowForm j)))
    (complexMatrix (closureKernel j)) (legVertex_available (direction_correction _))
    (legVertex_available (direction_correction _)) (pairVertex_available (closureKernel_available j))
  simpa only [Tensor.reindex_refl] using hn

theorem row_exit (j : Fin 48) :
    Exit (OctahedralSeparator.Direction (rowForm j)) (complexTensor (coefficientCard (rowForm j) (rowBase j))) := by
  by_cases ho : outsideRow j
  · exact Or.inr (Or.inr ⟨complexMatrix (outsideValues j),outside_bounded j ho,
      outside_nonsingular j ho,outside_transfer_not_direction j ho⟩)
  · by_cases he : j=34
    · subst j
      refine Or.inr (Or.inl ⟨embed (coeff (3/8) (1/4) 0 0),equality_output_scale_nonzero,?_⟩)
      rw [← equality_output]
      exact endpoint_bounded 34 ho
    · exact Or.inl ⟨complexTensor (endpointOutput j),endpoint_bounded j ho,
        endpoint_eightVertex j ho,endpoint_rank_two j ho⟩

theorem all_regular (f : Form) (frame : Fin 4) (order : Fin 6) : Exit (OctahedralSeparator.Direction f) (output f frame order) := by
  simpa only [regularRow_form,regularRow_base,output] using
    row_exit (regularRow f (frames frame (permutations order 0)))

def deficientOutput (f : Fin 2) (p : Fin 6) : Signature ℂ 4 :=
  complexTensor (coefficientCard (mixedForm f) (Fin.natAdd 9 p))

theorem all_mixed_deficient (f : Fin 2) (p : Fin 6) :
    Exit (OctahedralSeparator.Direction (mixedForm f)) (deficientOutput f p) := by
  simpa only [deficientRow_form,deficientRow_base,deficientOutput] using row_exit (deficientRow f p)

end Octahedral

namespace Icosahedral
open Holant.Certificates.IcosahedralSeparator

theorem standard (i : Fin 30) : Exit (fun U => groupDirection .icosahedral U) (uniformOutput i) := by
  refine Or.inr (Or.inr ⟨subsequentOutput i,?_,uniform_subsequent_nonsingular i,uniform_subsequent_outside i⟩)
  have h := PlatonicQuaternaryExits.Native.contract_bounded (fun U => groupDirection .icosahedral U)
    (Equiv.refl _) (uniformOutput i) subsequentKernel (quaternion_axis_direction .icosahedral 0)
    (by simpa only [nativeTransfer_eq_multiply] using
      Holant.Certificates.IcosahedralSeparator.Native.pair_available subsequentKernel_group)
  have ht : binarySignature (subsequentOutput i)=Signature.contract subsequentKernel (uniformOutput i) := by
    funext x
    change Signature.contract subsequentKernel (uniformOutput i) ![x 0,x 1]=_
    congr 1
    funext j
    fin_cases j <;> rfl
  simpa only [Tensor.reindex_refl,ht] using h

theorem opposite (i : Fin 30) : Exit OppositeIcosahedral.Direction (Opposite.output i) := by
  refine Or.inr (Or.inr ⟨Opposite.finalOutput i,?_,opposite_output_nonsingular i,opposite_output_outside i⟩)
  have h := PlatonicQuaternaryExits.Native.contract_bounded OppositeIcosahedral.Direction
    (Equiv.refl _) (Opposite.output i) Opposite.secondKernel
    (OppositeIcosahedral.Direction.of_tetrahedral (quaternion_axis_direction .tetrahedral 0))
    (Opposite.pair_available _ opposite_kernels_actual.2)
  have ht : binarySignature (Opposite.finalOutput i)=Signature.contract Opposite.secondKernel (Opposite.output i) := by
    funext x
    change Signature.contract Opposite.secondKernel (Opposite.output i) ![x 0,x 1]=_
    congr 1
    funext j
    fin_cases j <;> rfl
  simpa only [Tensor.reindex_refl,ht] using h

end Icosahedral
end
end Holant.Certificates.PlatonicQuaternaryExits
