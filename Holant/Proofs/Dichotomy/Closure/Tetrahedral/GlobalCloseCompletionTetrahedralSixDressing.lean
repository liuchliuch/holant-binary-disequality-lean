import Holant.Proofs.Dichotomy.Closure.Tetrahedral.GlobalCloseCompletionTetrahedralSixNormalization
import Holant.Certificates.OctahedralSeparator.TensorTransport

/-! Exact six-port coordinate dressing and contraction covariance.
Only the actual linear contraction map and physical port permutation occur. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionTetrahedralSix.Normalization
open Holant Holant.Certificates Holant.Certificates.MatchingProductBridge
open Holant.Certificates.RainbowOrbit Holant.Certificates.PlatonicIncidence
open Holant.Platonic.RankDeficientLocalization.Normalization

def actualMap (h : Signature ℂ 6) : Binary →ₗ[ℂ] FourTensor where
  toFun K := Signature.contract K h
  map_add' K L := by
    funext x
    simp [Signature.contract,add_mul,Finset.sum_add_distrib]
  map_smul' c K := by
    funext x
    simp [Signature.contract,mul_assoc,Finset.mul_sum]
    ring

@[simp] theorem actualMap_apply (h : Signature ℂ 6) (K : Binary) :
    actualMap h K = Signature.contract K h := rfl

structure SixDressing where
  left : Mat
  right : Mat
  swap : Bool
  residual : Legs

def SixDressing.portOrder (D : SixDressing) : Equiv.Perm (Fin 6) :=
  if D.swap then Equiv.swap 0 1 else Equiv.refl _
def SixDressing.legs (D : SixDressing) : Fin 6 → Mat :=
  Fin.cons D.left.transpose (Fin.cons D.right D.residual)
def SixDressing.tensor (D : SixDressing) (h : Signature ℂ 6) : Signature ℂ 6 :=
  Tensor.reindex D.portOrder (Signature.coordinateAction D.legs h)

def SixDressing.ofDomain {g : PlatonicModel} (D : DomainAction g) (L : Legs) : SixDressing :=
  ⟨D.left,D.right,D.swap,L⟩

theorem contract_pair_swap (h : Signature ℂ 6) (K : Mat) :
    Signature.contract K (Tensor.reindex (Equiv.swap (0 : Fin 6) 1) h)=
      Signature.contract K.transpose h := by
  funext x
  have hcons (a b : Bool) :
      (fun j : Fin 6 => (Fin.cons a (Fin.cons b x) : Fin 6 → Bool) (Equiv.swap (0 : Fin 6) 1 j))=
        Fin.cons b (Fin.cons a x) := by
    funext j
    fin_cases j <;> simp [Equiv.swap_apply_def] <;> rfl
  simp only [Signature.contract,Tensor.reindex,hcons,Matrix.transpose_apply]
  rw [Finset.sum_comm]

theorem SixDressing.card (D : SixDressing) (h : Signature ℂ 6) (K : Mat) :
    Signature.contract K (D.tensor h)=act D.residual
      (Signature.contract (D.left*(if D.swap then K.transpose else K)*D.right) h) := by
  have hk (K : Mat) :
      OctahedralSeparator.pairKernel D.left.transpose D.right K=D.left*K*D.right := by
    ext a b
    simp [OctahedralSeparator.pairKernel,Kernel.mul,Kernel.transpose,Matrix.mul_apply,
      Fintype.sum_bool]
    ring
  cases hs : D.swap
  · simp only [SixDressing.tensor,SixDressing.portOrder,hs,Bool.false_eq_true,if_false,
      Tensor.reindex_refl]
    rw [OctahedralSeparator.contract_action]
    change act D.residual (Signature.contract
      (OctahedralSeparator.pairKernel D.left.transpose D.right K) h)=_
    rw [hk]
  · simp only [SixDressing.tensor,SixDressing.portOrder,hs,if_true]
    rw [contract_pair_swap,OctahedralSeparator.contract_action]
    change act D.residual (Signature.contract
      (OctahedralSeparator.pairKernel D.left.transpose D.right K.transpose) h)=_
    rw [hk]

theorem ofDomain_actualMap {g : PlatonicModel} (D : DomainAction g) (L : Legs)
    (h : Signature ℂ 6) :
    actualMap ((SixDressing.ofDomain D L).tensor h)=
      dressedMap D L (actualMap h) := by
  apply LinearMap.ext
  intro K
  exact (SixDressing.ofDomain D L).card h K


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionTetrahedralSix.Normalization
end
