import Holant.Certificates.PlatonicBridgeInterface.OctahedralSource

/-! Fixed actual current-form kernels and bounded native networks for every
full-rank physical map recovered from the unrestricted source hypotheses. -/
namespace Holant.Certificates.PlatonicBridgeInterface.Octahedral
open Holant Holant.Certificates.MatchingProductBridge
open Holant.Certificates.OctahedralSeparator
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-- K_O=Q0+Q1 and K_f=theta_f(K_O), with the source's literal representative. -/
def fixedKernel (f : Form) : Binary := complexMatrix (theta f firstKernel)

theorem fixedKernel_theta (f : Form) : fixedKernel f = thetaEquiv f (Q0+Q1) := by
  unfold fixedKernel firstKernel
  rw [complexMatrix_theta,complexMatrix_add,complexMatrix_q,complexMatrix_q]
  rfl

theorem fixedKernel_standard : fixedKernel 0 = Q0+Q1 := by
  unfold fixedKernel
  have h : theta 0 firstKernel = firstKernel := by
    change mm (q 0) (mm firstKernel (q 0)) = firstKernel
    simp
  rw [h]
  unfold firstKernel
  rw [complexMatrix_add,complexMatrix_q,complexMatrix_q]
  rfl

theorem fixedKernel_available (f : Form) : Direction f (Matrix.of (fixedKernel f)) :=
  firstKernel_available f

def FixedKernelExit (f : Form) (h : Signature ℂ 6) : Prop :=
  (∃ t : Signature ℂ 4, BoundedNativeRealization f h (fixedKernel f) t ∧
    TetrahedralOrientation.EndpointNondegenerateEightVertex t ∧
    ∀ r : Fin 3, (flatten r t).rank = 2) ∨
  (∃ c : ℂ, c ≠ 0 ∧ BoundedNativeRealization f h (fixedKernel f) (c • complexEq4)) ∨
  ∃ B : Native.Binary,
    BoundedNativeRealization f h (fixedKernel f) (Native.binarySignature B) ∧
    Matrix.det (Matrix.of B) ≠ 0 ∧ ¬Direction f (nativeTransfer B)

theorem actual_fixed_kernel_exit (f : Form) (h : Signature ℂ 6)
    (hn : SourceHypotheses f (actualMap h)) (hr : mapRank (actualMap h) = 4) :
    FixedKernelExit f h := by
  obtain ⟨i,hi⟩ := actual_full_card_map f h hn hr
  let frame : Fin 4 := ⟨i.val/6,by omega⟩
  let order : Fin 6 := ⟨i.val%6,by omega⟩
  let j := regularRow f (OctahedralSeparator.frames frame (permutations order 0))
  have hjf : rowForm j = f := regularRow_form _ _
  have hcard : Signature.contract (fixedKernel f) (Tensor.reindex (Equiv.refl _) h) =
      complexTensor (coefficientCard (rowForm j) (rowBase j)) := by
    simpa only [fixedKernel,j,regularRow_form,regularRow_base,Tensor.reindex_refl] using
      normalized_first_card f frame order h hi
  have hK : Direction (rowForm j) (Matrix.of (fixedKernel f)) := by
    rw [hjf]
    exact fixedKernel_available f
  have hresult : FixedKernelExit (rowForm j) h := by
    have heK : fixedKernel (rowForm j) = fixedKernel f := congrArg fixedKernel hjf
    by_cases ho : outsideRow j
    · apply Or.inr ∘ Or.inr
      refine ⟨complexMatrix (outsideValues j),?_,outside_nonsingular j ho,
        outside_transfer_not_direction j ho⟩
      rw [heK]
      exact bounded_outside_network j ho h (Equiv.refl _) _ hK hcard
    · by_cases he : j = 34
      · apply Or.inr ∘ Or.inl
        refine ⟨embed (coeff (3/8) (1/4) 0 0),equality_output_scale_nonzero,?_⟩
        have hEq : complexTensor (endpointOutput j) =
            embed (coeff (3/8) (1/4) 0 0) • complexEq4 := by
          rw [he]
          exact equality_output
        rw [←hEq,heK]
        exact bounded_endpoint_network j ho h (Equiv.refl _) _ hK hcard
      · apply Or.inl
        refine ⟨complexTensor (endpointOutput j),?_,endpoint_eightVertex j ho,endpoint_rank_two j ho⟩
        rw [heK]
        exact bounded_endpoint_network j ho h (Equiv.refl _) _ hK hcard
  simpa only [hjf] using hresult

theorem actual_unmixed_fixed_endpoint (f : Fin 2) (h : Signature ℂ 6)
    (hn : SourceHypotheses (f.castAdd 2) (actualMap h)) (hr : mapRank (actualMap h) = 4) :
    ∃ t : Signature ℂ 4, BoundedNativeRealization (f.castAdd 2) h (fixedKernel (f.castAdd 2)) t ∧
      TetrahedralOrientation.EndpointNondegenerateEightVertex t ∧
      ∀ r : Fin 3, (flatten r t).rank = 2 := by
  obtain ⟨i,hi⟩ := actual_full_card_map (f.castAdd 2) h hn hr
  let frame : Fin 4 := ⟨i.val/6,by omega⟩
  let order : Fin 6 := ⟨i.val%6,by omega⟩
  let j := regularRow (f.castAdd 2) (OctahedralSeparator.frames frame (permutations order 0))
  have ho : ¬outsideRow j := standard_prime_rows f _
  have hcard : Signature.contract (fixedKernel (f.castAdd 2)) (Tensor.reindex (Equiv.refl _) h) =
      complexTensor (coefficientCard (rowForm j) (rowBase j)) := by
    simpa only [fixedKernel,j,regularRow_form,regularRow_base,Tensor.reindex_refl] using
      normalized_first_card (f.castAdd 2) frame order h hi
  have hK : Direction (rowForm j) (Matrix.of (fixedKernel (f.castAdd 2))) := by
    simpa only [j,regularRow_form] using fixedKernel_available (f.castAdd 2)
  refine ⟨complexTensor (endpointOutput j),?_,endpoint_eightVertex j ho,endpoint_rank_two j ho⟩
  simpa only [j,regularRow_form] using bounded_endpoint_network j ho h (Equiv.refl _) _ hK hcard

end
end Holant.Certificates.PlatonicBridgeInterface.Octahedral
