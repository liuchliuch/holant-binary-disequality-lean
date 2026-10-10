import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinTwistedAlgebra
import Holant.Proofs.Dichotomy.Closure.A0.GlobalCloseCompletionA0KernelRealizes
import Holant.Proofs.Dichotomy.Closure.B.GlobalCloseCompletionBEqualityRealizes
import Holant.Proofs.Dichotomy.Closure.Sparse.GlobalCloseCompletionSparseEq4Flip

/-! The two-copy sparse identity uses actual projective Pauli Z and retained I.
Two further native copies square the compressed trace-zero matrix; the resulting
nonzero scalar DEQ is turned into literal Eq4 by two actual I legs. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinTwistedActual
open Holant Holant.Tractable Holant.OpenNetworkComposition
open Holant.OpenNetworkComposition.ProjectiveSubstitution
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.EightVertex.ProductAnchor
namespace T
export GlobalCloseCompletionKleinTwistedAlgebra (Z normal sparse twisted twisted_normal planeWord planeOrder compressed sparse_plane compressed_square)
end T
namespace C
export GeneralEOAffinePlaneChain (series series_denote series_uses series_native binary table Mat)
end C
namespace E
export GlobalCloseCompletionSparseEq4Flip (identity leg leg_native equality_denote)
end E
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type*} [Field K]

private theorem contract_Z {n : ℕ} (F : SignatureFamily K) (hI : RetainsIdentity F)
    (hZ : Gadget.RealizesUpTo F .disequality (fun x : Fin 2→Bool=>T.Z (x 0) (x 1)))
    (q : Signature K (n+2)) (hq : Gadget.RealizesUpTo F .disequality q) :
    Gadget.RealizesUpTo F .disequality (Signature.contract T.Z q) := by
  obtain ⟨c,hc,hZ⟩ := hZ
  let B : Matrix Bool Bool K := Matrix.of (fun b d=>c*T.Z b d)
  have hB : Gadget.Realizes F .disequality
      (Holant.Certificates.MatchingContractionClosure.binarySignature B) := hZ
  have hr := GlobalCloseCompletionA0KernelRealizes.contract_upTo B F hI hB q hq
  have edge : GlobalCloseCompletionA0KernelRealizes.edge B=fun b d=>(-c)*T.Z b d := by
    funext b d
    cases b <;> cases d <;>
      simp [B,GlobalCloseCompletionA0KernelRealizes.edge,Holant.Certificates.MatchingContractionClosure.X,
        Matrix.mul_apply,T.Z,Signature.disequality]
  obtain ⟨s,hs,hr⟩ := hr
  refine ⟨s*(-c),mul_ne_zero hs (neg_ne_zero.mpr hc),?_⟩
  convert hr using 1
  funext x
  rw [edge]
  simp only [Signature.contract,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro d _
  ring

theorem twisted_actual (F : SignatureFamily K) (hI : RetainsIdentity F)
    (hZ : Gadget.RealizesUpTo F .disequality (fun x : Fin 2→Bool=>T.Z (x 0) (x 1)))
    (q : Signature K 4) (hq : Gadget.RealizesUpTo F .disequality q) :
    Gadget.RealizesUpTo F .disequality (T.twisted q) := by
  have pair := realizesUpTo_tensor F .disequality q q hq hq
  have reordered := realizesUpTo_reindex F (wiringEquiv ![false,false,true,true]).symm _ pair
  exact GlobalCloseCompletionBEqualityRealizes.contract_upTo F hI _
    (contract_Z F hI hZ _ reordered)

private theorem splice_identity {n : ℕ} (q : Signature K n) (i : Fin n) :
    spliceTensor q OrdinaryNormalization.identitySignature i=
      fun x=>q (Function.update x i (!(x i))) := by
  funext x
  cases hx : x i <;>
    simp [spliceTensor,OrdinaryNormalization.identitySignature,Signature.equality,
      Signature.disequality,hx]

private theorem flip_actual (F : SignatureFamily K) (hI : RetainsIdentity F)
    {n : ℕ} (q : Signature K n) (hq : Gadget.RealizesUpTo F .disequality q) (i : Fin n) :
    Gadget.RealizesUpTo F .disequality (fun x=>q (Function.update x i (!(x i)))) := by
  obtain ⟨c,hc,hq⟩ := hq
  refine ⟨c,hc,?_⟩
  have hs := realizes_splice F _ _ hq (Gadget.realizes_of_mem F .disequality _ hI) i
  rwa [splice_identity] at hs

theorem plane_actual (F : SignatureFamily K) (hI : RetainsIdentity F)
    (q : Signature K 4) (hq : Gadget.RealizesUpTo F .disequality q) :
    Gadget.RealizesUpTo F .disequality (fun x=>q (T.planeWord x)) := by
  have hr := realizesUpTo_reindex F T.planeOrder q hq
  have hf := flip_actual F hI _ (flip_actual F hI _ hr 1) 3
  convert hf using 1
  funext x
  apply congrArg q
  funext i
  fin_cases i <;> simp [T.planeOrder,T.planeWord,Tensor.reindex_apply,Function.update,Equiv.swap_apply_def]

theorem traceZero_eq4 (F : SignatureFamily K) (hI : RetainsIdentity F) (a c : K)
    (actual : Gadget.RealizesUpTo F .disequality (EOBinaryPlaneCore.lift (T.compressed a c)))
    (separated : a^2≠c^2) :
    Gadget.RealizesUpTo F .disequality (equalityFour (K:=K)) := by
  obtain ⟨r,hr,actual⟩ := actual
  obtain ⟨N,uses,native,denote⟩ := OrdinaryNormalization.realizes_exists_ordinary hI actual
  let A : C.Mat (K:=K) := r • C.table (T.compressed a c)
  have hN : N.denote=EOBinaryPlaneCore.lift (C.binary A) := by
    rw [denote]
    funext x
    simp only [EOBinaryPlaneCore.lift]
    split_ifs with h
    · congr 1
      cases h0 : x 0 <;> cases h2 : x 2 <;>
        simp [A,C.binary,C.table,GeneralEOAffinePlaneChain.bitIndex,T.compressed,h0,h2]
    · simp
  have square : A*A=(r^2*(a^2-c^2)) • (1 : C.Mat (K:=K)) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [A,C.table,T.compressed,Matrix.mul_apply,Fin.sum_univ_two] <;> ring
  have hs := C.series_denote N N A A hN hN
  rw [square,GeneralEOAffinePlaneDEQ.lifted_scalar] at hs
  let S := C.series N N
  have source : Gadget.Realizes F .disequality ((r^2*(a^2-c^2)) • ExactTwoSignatures.E) := by
    rw [←hs]
    exact Gadget.realizes_network S F .disequality (C.series_uses N N F uses uses)
      (C.series_native N N native native)
  have deq : Gadget.RealizesUpTo F .disequality (ExactTwoSignatures.E (K:=K)) :=
    ⟨r^2*(a^2-c^2),mul_ne_zero (pow_ne_zero _ hr) (sub_ne_zero.mpr separated),source⟩
  have flip := flip_actual F hI _ (flip_actual F hI _ deq 1) 3
  convert flip using 1
  funext x
  rw [ExactTwoSignatures.E_reference]
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [Function.update,equalityFour,Fin.forall_fin_succ,h0,h1,h2,h3]

theorem normal_eq4 (F : SignatureFamily K) (hI : RetainsIdentity F)
    (hZ : Gadget.RealizesUpTo F .disequality (fun x : Fin 2→Bool=>T.Z (x 0) (x 1)))
    (a b c d : K) (actual : Gadget.RealizesUpTo F .disequality (T.normal a b c d))
    (separated : (a^2-b^2)^2≠(c^2-d^2)^2) :
    Gadget.RealizesUpTo F .disequality (equalityFour (K:=K)) := by
  have sparse := twisted_actual F hI hZ _ actual
  rw [T.twisted_normal] at sparse
  have plane := plane_actual F hI _ sparse
  rw [T.sparse_plane] at plane
  exact traceZero_eq4 F hI _ _ plane separated

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinTwistedActual
end
