import Holant.Platonic.RankDeficientLocalization.Normalization.MapNormalization
import Holant.Certificates.PlatonicDeficient.EncodedOutputs

/-! Lifting the map normalization to six physical ports, then absorbing all
its operations into one ordinary contraction graph containing the original h. -/
namespace Holant.Platonic.RankDeficientLocalization.Normalization
open Holant Holant.Certificates Holant.Certificates.MatchingProductBridge
open Holant.Certificates.RainbowOrbit Holant.Certificates.PlatonicIncidence
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

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
    PlatonicBridgeInterface.Octahedral.actualMap ((SixDressing.ofDomain D L).tensor h)=
      dressedMap D L (PlatonicBridgeInterface.Octahedral.actualMap h) := by
  apply LinearMap.ext
  intro K
  exact (SixDressing.ofDomain D L).card h K

/-- The final source contraction is ports1/3 of the normalized signature. -/
def SixDressing.finalOrder (D : SixDressing) : Equiv.Perm (Fin 6) :=
  D.portOrder.trans (TetrahedralDeck.portOrder 1).symm

def SixDressing.finalKernel (D : SixDressing) : Mat :=
  OctahedralSeparator.pairKernel (D.legs (D.finalOrder.symm 0))
    (D.legs (D.finalOrder.symm 1)) Q0

def SixDressing.finalLegs (D : SixDressing) : Legs :=
  fun j => D.legs (D.finalOrder.symm j.succ.succ)

def SixDressing.network (D : SixDressing) (h : Signature ℂ 6) : Network ℂ 4 :=
  OctahedralSeparator.Native.orderedDressedNetwork D.finalOrder h D.finalKernel D.finalLegs

theorem SixDressing.network_denote (D : SixDressing) (h : Signature ℂ 6) :
    (D.network h).denote=Signature.contract Q0
      (Tensor.reindex (TetrahedralDeck.portOrder 1).symm (D.tensor h)) := by
  rw [SixDressing.network,OctahedralSeparator.Native.orderedDressedNetwork_denote,SixDressing.tensor,
    Tensor.reindex_trans,OctahedralSeparator.reindex_action,OctahedralSeparator.contract_action]
  rfl

/-- The ancestor label is literally the original input tensor, even if its
contracted pair was reversed during normalization. -/
theorem SixDressing.network_ancestor (D : SixDressing) (h : Signature ℂ 6) :
    (D.network h).vertex (0 : Fin 6)=h := OctahedralSeparator.Native.orderedDressedNetwork_ancestor _ _ _ _

theorem SixDressing.network_counts (D : SixDressing) (h : Signature ℂ 6) :
    (D.network h).shape.vertices=6 ∧ (D.network h).shape.edges=6 ∧
      (Finset.univ.filter (fun v => (D.network h).shape.arity v=6)).card=1 ∧
      (Finset.univ.filter (fun v => (D.network h).shape.arity v=2)).card=5 :=
  ⟨rfl,rfl,OctahedralSeparator.Native.orderedDressedNetwork_ancestor_vertices _ _ _ _,
    OctahedralSeparator.Native.orderedDressedNetwork_binary_vertices _ _ _ _⟩

theorem ofDomain_legs_mem {g : PlatonicModel} (D : DomainAction g) (L : Legs)
    (hL : GroupLegs g L) : ∀j,groupDirection g ((SixDressing.ofDomain D L).legs j) := by
  intro j
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => hL k) j) j
  · exact direction_transpose g D.left_mem
  · exact D.right_mem

theorem SixDressing.finalKernel_mem (g : PlatonicModel) (D : SixDressing)
    (hD : ∀j,groupDirection g (D.legs j)) : groupDirection g D.finalKernel := by
  have hk : D.finalKernel=(D.legs (D.finalOrder.symm 0)).transpose*
      (Matrix.of Q0)*(D.legs (D.finalOrder.symm 1)) := by
    ext a b
    simp [SixDressing.finalKernel,OctahedralSeparator.pairKernel,Kernel.mul,Kernel.transpose,
      Matrix.mul_apply,Fintype.sum_bool]
  rw [hk]
  exact groupDirection_mul g (groupDirection_mul g (direction_transpose g (hD _))
    (quaternion_axis_direction g 0)) (hD _)

theorem SixDressing.network_resources (g : PlatonicModel) (D : SixDressing)
    (hD : ∀j,groupDirection g (D.legs j)) (h : Signature ℂ 6) :
    ∀v,(⟨(D.network h).shape.arity v,(D.network h).vertex v⟩ : AnySignature ℂ) ∈
      PlatonicDeficient.standardResources g h := by
  have hp : groupDirection g (OctahedralSeparator.nativeTransfer (OctahedralSeparator.Native.pairVertex D.finalKernel)) := by
    rw [OctahedralSeparator.nativeTransfer_pairVertex]
    exact groupDirection_mul g (X_direction g) (D.finalKernel_mem g hD)
  have hl (j : Fin 4) : groupDirection g
      (OctahedralSeparator.nativeTransfer (OctahedralSeparator.Native.legVertex (D.finalLegs j))) := by
    rw [OctahedralSeparator.nativeTransfer_legVertex]
    exact hD _
  intro v
  fin_cases v
  · exact Or.inl (by congr 1; exact D.network_ancestor h)
  · exact Or.inr ⟨_,rfl,hp⟩
  · exact Or.inr ⟨_,rfl,hl 0⟩
  · exact Or.inr ⟨_,rfl,hl 1⟩
  · exact Or.inr ⟨_,rfl,hl 2⟩
  · exact Or.inr ⟨_,rfl,hl 3⟩

end
end Holant.Platonic.RankDeficientLocalization.Normalization
