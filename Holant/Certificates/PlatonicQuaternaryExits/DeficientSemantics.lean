import Holant.Certificates.PlatonicQuaternaryExits.DeficientData
import Holant.Certificates.PlatonicQuaternaryExits.Regular

namespace Holant.Certificates.PlatonicQuaternaryExits.Deficient
open Holant Holant.Certificates.OctahedralSeparator
open Holant.Certificates.MatchingProductBridge
open Holant.Certificates.OctahedralSeparator.Native (binarySignature pairVertex)
noncomputable section
set_option backward.isDefEq.respectTransparency false

private theorem pair_equality (g : PlatonicModel) :
    groupDirection g (nativeTransfer (pairVertex Q0)) := by
  have he : pairVertex Q0=Q0 := by
    funext a b
    cases a <;> cases b <;> rfl
  rw [he]
  rw [nativeTransfer_eq_multiply]
  exact Q0_X_direction g

theorem standard_binary_exact (p : Fin 6) :
    binarySignature (complexMatrix (standardBinary p))=Signature.contract Q0 (output p) := by
  have h0 : complexMatrix (q 0)=Q0 := complexMatrix_q 0
  rw [output,←h0,←complexTensor_contract]
  funext x
  change embed (standardBinary p (x 0) (x 1))=embed (Signature.contract (q 0) (deficientCard p) x)
  apply congrArg embed
  rw [standard_binary_check,cached_deficient]
  congr 1
  funext j
  fin_cases j <;> rfl

theorem octahedral_binary_exact (p : Fin 6) :
    binarySignature (complexMatrix (octahedralBinary p))=
      Signature.contract Q0 (Tensor.reindex order24 (output p)) := by
  have h0 : complexMatrix (q 0)=Q0 := complexMatrix_q 0
  rw [output,←h0,←complexTensor_reindex,←complexTensor_contract]
  funext x
  change embed (octahedralBinary p (x 0) (x 1))=
    embed (Signature.contract (q 0) (Tensor.reindex order24 (deficientCard p)) x)
  apply congrArg embed
  rw [octahedral_binary_check,cached_deficient]
  congr 1
  funext j
  fin_cases j <;> rfl

theorem prime_binary_exact (p : Fin 6) :
    binarySignature (complexMatrix (primeBinary p))=
      Signature.contract (complexMatrix primeKernel) (primeOutput p) := by
  rw [primeOutput,←complexTensor_contract]
  funext x
  change embed (primeBinary p (x 0) (x 1))=embed (Signature.contract primeKernel (primeTensor p) x)
  apply congrArg embed
  rw [prime_binary_check]
  congr 1
  funext j
  fin_cases j <;> rfl

theorem standard_nonsingular (p : Fin 6) : (complexMatrix (standardBinary p)).det≠0 := by
  rw [←embed_determinant,standard_determinant]
  exact embed_ne_zero (by decide +kernel)

theorem octahedral_nonsingular (p : Fin 6) : (complexMatrix (octahedralBinary p)).det≠0 := by
  rw [←embed_determinant,octahedral_determinant]
  exact embed_ne_zero (by decide +kernel)

theorem prime_nonsingular (p : Fin 6) : (complexMatrix (primeBinary p)).det≠0 := by
  rw [←embed_determinant,prime_determinant]
  exact embed_ne_zero (by decide +kernel)

/-- Soundness of projective cross-product rejection, with the literal current
group pulled back only for the membership test, never for a gadget. -/
theorem outside_of_different (f : Form) (U : Mat)
    (hd : ∀ k : Fin 24, ∃ a b c d : Bool,
      pull f (mm U flip) a b*standard k c d≠pull f (mm U flip) c d*standard k a b) :
    ¬OctahedralSeparator.Direction f (nativeTransfer (complexMatrix U)) := by
  rw [embedded_nativeTransfer]
  rintro ⟨c,hc,k,he⟩
  have hp : complexMatrix (pull f (mm U flip))=c • complexMatrix (standard k) := by
    rw [complexMatrix_pull,he,complexPull_smul,complexMatrix_theta,complexPull_complexTheta]
  obtain ⟨a,b,d,e,hn⟩ := hd k
  have h1 := congrArg (fun M : Matrix Bool Bool ℂ => M a b) hp
  have h2 := congrArg (fun M : Matrix Bool Bool ℂ => M d e) hp
  change embed (pull f (mm U flip) a b)=c*embed (standard k a b) at h1
  change embed (pull f (mm U flip) d e)=c*embed (standard k d e) at h2
  apply hn
  apply embed_injective
  rw [embed_mul,embed_mul,h1,h2]
  ring

theorem octahedral_outside (p : Fin 6) :
    ¬OctahedralSeparator.Direction 0 (nativeTransfer (complexMatrix (octahedralBinary p))) := by
  apply outside_of_different
  simpa [pull,conjugator,inverseConjugator] using octahedral_different p

theorem prime_outside (p : Fin 6) :
    ¬OctahedralSeparator.Direction 1 (nativeTransfer (complexMatrix (primeBinary p))) :=
  outside_of_different 1 _ (prime_different p)

namespace Golden
open Holant.Certificates.IcosahedralSeparator
open Holant.Certificates.RainbowOrbit
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem embed_binary (p : Fin 6) (a b : Bool) :
    gembed (binaryCode (index p) a b)=4*complexMatrix (standardBinary p) a b := by
  fin_cases p <;> cases a <;> cases b <;>
    norm_num [binaryCode,index,realPart,imagPart,gembed,GoldenInt.ofInt,GoldenInt.eval,
      standardBinary,mat,rat,complexMatrix,embed_coeff,embed_zero]
  all_goals ring

theorem embed_transfer (p : Fin 6) (a b : Bool) :
    gembed (transferCode (index p) a b)=4*nativeTransfer (complexMatrix (standardBinary p)) a b := by
  rw [transferCode,embed_binary]
  simp only [nativeTransfer,Kernel.mul_disequality,Matrix.of_apply]

theorem standard_outside (p : Fin 6) :
    ¬groupDirection .icosahedral (nativeTransfer (complexMatrix (standardBinary p))) := by
  intro h
  obtain ⟨j,c,hc,he⟩ := (complete .icosahedral _).mp h
  obtain ⟨a,b,d,e,hn⟩ := different (index p) j
  apply gembed_ne_zero hn
  rw [gembed_sub,gembed_mul,gembed_mul,embed_transfer,embed_transfer,
    gembed_groupCode,gembed_groupCode]
  have h1 := congrArg (fun M : Matrix Bool Bool ℂ => M a b) he
  have h2 := congrArg (fun M : Matrix Bool Bool ℂ => M d e) he
  change nativeTransfer (complexMatrix (standardBinary p)) a b=c*representative .icosahedral j a b at h1
  change nativeTransfer (complexMatrix (standardBinary p)) d e=c*representative .icosahedral j d e at h2
  rw [h1,h2]
  ring

end Golden

theorem tetrahedral_outside (p : Fin 6) :
    ¬groupDirection .tetrahedral (nativeTransfer (complexMatrix (standardBinary p))) := by
  rintro ⟨c,hc,V,hV,he⟩
  exact Golden.standard_outside p ⟨c,hc,V,Or.inl hV,he⟩

theorem tetrahedral (p : Fin 6) : Exit (fun U => groupDirection .tetrahedral U) (output p) := by
  refine Or.inr (Or.inr ⟨complexMatrix (standardBinary p),?_,standard_nonsingular p,tetrahedral_outside p⟩)
  rw [standard_binary_exact]
  simpa only [Tensor.reindex_refl] using PlatonicQuaternaryExits.Native.contract_bounded
    (fun U => groupDirection .tetrahedral U) (Equiv.refl _) (output p) Q0
    (quaternion_axis_direction .tetrahedral 0) (pair_equality .tetrahedral)

theorem icosahedral (p : Fin 6) : Exit (fun U => groupDirection .icosahedral U) (output p) := by
  refine Or.inr (Or.inr ⟨complexMatrix (standardBinary p),?_,standard_nonsingular p,Golden.standard_outside p⟩)
  rw [standard_binary_exact]
  simpa only [Tensor.reindex_refl] using PlatonicQuaternaryExits.Native.contract_bounded
    (fun U => groupDirection .icosahedral U) (Equiv.refl _) (output p) Q0
    (quaternion_axis_direction .icosahedral 0) (pair_equality .icosahedral)

theorem octahedral (p : Fin 6) : Exit (OctahedralSeparator.Direction 0) (output p) := by
  refine Or.inr (Or.inr ⟨complexMatrix (octahedralBinary p),?_,octahedral_nonsingular p,octahedral_outside p⟩)
  rw [octahedral_binary_exact]
  exact PlatonicQuaternaryExits.Native.contract_bounded _ order24 (output p) Q0
    (by simpa [complexMatrix_q,quaternionBasis,Q0] using direction_identity 0)
    (OctahedralSeparator.pairVertex_available (by simpa [complexMatrix_q,quaternionBasis,Q0] using direction_identity 0))

theorem prime (p : Fin 6) : Exit (OctahedralSeparator.Direction 1) (primeOutput p) := by
  refine Or.inr (Or.inr ⟨complexMatrix (primeBinary p),?_,prime_nonsingular p,prime_outside p⟩)
  rw [prime_binary_exact]
  simpa only [Tensor.reindex_refl] using PlatonicQuaternaryExits.Native.contract_bounded _ (Equiv.refl _) (primeOutput p)
    (complexMatrix primeKernel) (by simpa [complexMatrix_q,quaternionBasis,Q0] using direction_identity 1)
    (OctahedralSeparator.pairVertex_available (OctahedralSeparator.Direction.standard 1 11))

namespace Opposite
open Holant.Certificates.OppositeIcosahedral

def output (p : Fin 6) : Signature ℂ 4 := transport (Deficient.output p)
def kernel : Matrix Bool Bool ℂ := kappa Q0
def binary (p : Fin 6) : Matrix Bool Bool ℂ := binaryTransport (complexMatrix (standardBinary p))

theorem kernel_actual : OppositeIcosahedral.Direction kernel :=
  (kernel_membership_iff _).mpr (quaternion_axis_direction .icosahedral 0)

theorem binary_exact (p : Fin 6) : binarySignature (binary p)=Signature.contract kernel (output p) := by
  rw [output,kernel,IcosahedralSeparator.Opposite.contract_transport,←standard_binary_exact]
  funext x
  have hx : x=![x 0,x 1] := by funext j; fin_cases j <;> rfl
  rw [hx,IcosahedralSeparator.Opposite.transport_binary]
  rfl

theorem nonsingular (p : Fin 6) : (binary p).det≠0 :=
  (binary_nonsingular_iff _).mpr (standard_nonsingular p)

theorem outside (p : Fin 6) : ¬OppositeIcosahedral.Direction (nativeTransfer (binary p)) :=
  (outside_transfer_iff _).mpr (Golden.standard_outside p)

theorem exit (p : Fin 6) : Exit OppositeIcosahedral.Direction (output p) := by
  refine Or.inr (Or.inr ⟨binary p,?_,nonsingular p,outside p⟩)
  rw [binary_exact]
  simpa only [Tensor.reindex_refl] using PlatonicQuaternaryExits.Native.contract_bounded _ (Equiv.refl _) (output p) kernel
    (OppositeIcosahedral.Direction.of_tetrahedral (quaternion_axis_direction .tetrahedral 0))
    (IcosahedralSeparator.Opposite.pair_available _ kernel_actual)

end Opposite
end
end Holant.Certificates.PlatonicQuaternaryExits.Deficient
