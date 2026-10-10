import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryProductInteraction

/-! The actual zero-cap tensor partitions force anchored binary interactions
to form a matching. A three-port fork would survive a fourth zero cap and
put three distinct original ports in one factor of arity at most two. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryInteractionMatching
open Holant
namespace I
export GlobalCloseCompletionUnaryProductInteraction (owner minor same_block_of_minor cap_minor)
end I
namespace P
export GlobalCloseCompletionUnaryPinnedProduct (cap)
end P
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option Elab.async false
variable {K : Type} [Field K] {n : ℕ}

def fiberPorts (D : TensorDecomposition K n) (v : Fin D.count) :
    Fin (D.arity v) ≃ {i : Fin n // I.owner D i=v} :=
  Equiv.ofBijective (fun k=>⟨D.ports ⟨v,k⟩,by simp [I.owner]⟩) (by
    constructor
    · intro i j equal
      have h:=D.ports.injective (congrArg Subtype.val equal)
      exact eq_of_heq (Sigma.mk.inj h).2
    · intro x
      obtain ⟨⟨v',k⟩,hp⟩:=D.ports.surjective x.val
      have hv : v'=v := by
        have h:=congrArg (I.owner D) hp
        simpa only [I.owner,Equiv.symm_apply_apply] using h.trans x.property
      subst v'
      exact ⟨k,Subtype.ext hp⟩)

theorem no_three (D : TensorDecomposition K n) (v : Fin D.count) (small : D.arity v≤2)
    (i j k : Fin n) (ij : i≠j) (ik : i≠k) (jk : j≠k)
    (hi : I.owner D i=v) (hj : I.owner D j=v) (hk : I.owner D k=v) : False := by
  classical
  let a : {i : Fin n // I.owner D i=v}:=⟨i,hi⟩
  let b : {i : Fin n // I.owner D i=v}:=⟨j,hj⟩
  let c : {i : Fin n // I.owner D i=v}:=⟨k,hk⟩
  have ab : a≠b := fun h=>ij (congrArg Subtype.val h)
  have ac : a≠c := fun h=>ik (congrArg Subtype.val h)
  have bc : b≠c := fun h=>jk (congrArg Subtype.val h)
  have lower : 3≤Fintype.card {i : Fin n // I.owner D i=v} := by
    calc
      3=({a,b,c} : Finset {i : Fin n // I.owner D i=v}).card := by simp [ab,ac,bc]
      _≤_:=Finset.card_le_univ _
  have equal:=Fintype.card_congr (fiberPorts D v)
  simp only [Fintype.card_fin] at equal
  omega

theorem small_no_fork (D : TensorDecomposition K n) (small : ∀v,D.arity v≤2)
    (i j k : Fin n) (ij : i≠j) (ik : i≠k) (jk : j≠k)
    (edge1 : I.minor D.value i j≠0) (edge2 : I.minor D.value i k≠0) : False :=
  no_three D (I.owner D i) (small _) i j k ij ik jk rfl
    (I.same_block_of_minor D i j edge1).symm (I.same_block_of_minor D i k edge2).symm

theorem fourth (large : 4≤n) (i j k : Fin n) : ∃l : Fin n,l≠i ∧ l≠j ∧ l≠k := by
  classical
  by_contra none
  have contained : (Finset.univ : Finset (Fin n))⊆{i,j,k} := by
    intro l _
    simp only [Finset.mem_insert,Finset.mem_singleton]
    by_contra absent
    apply none
    have h : l≠i ∧ l≠j ∧ l≠k := by tauto
    exact ⟨l,h⟩
  have bound:=Finset.card_le_card contained
  have top : ({i,j,k} : Finset (Fin n)).card≤3 := by
    have h1:=Finset.card_insert_le i ({j,k} : Finset (Fin n))
    have h2:=Finset.card_insert_le j ({k} : Finset (Fin n))
    simp only [Finset.card_singleton] at h2
    omega
  simp only [Finset.card_univ,Fintype.card_fin] at bound
  omega

/-- Every real all-small zero-cap factorization constrains the SAME original
coefficient graph. The matching conclusion has no supplied matching oracle. -/
theorem caps_no_fork (f : Signature K n) (large : 4≤n)
    (caps : ∀l,Signature.TensorClosure (fun m (_ : Signature K m)=>m≤2) (P.cap l f))
    (i j k : Fin n) (ij : i≠j) (ik : i≠k) (jk : j≠k)
    (edge1 : I.minor f i j≠0) (edge2 : I.minor f i k≠0) : False := by
  obtain ⟨l,li,lj,lk⟩:=fourth large i j k
  obtain ⟨D,small,equation⟩:=caps l
  apply small_no_fork D small i j k ij ik jk
  · rw [equation,I.cap_minor f i j l li.symm lj.symm]
    exact edge1
  · rw [equation,I.cap_minor f i k l li.symm lk.symm]
    exact edge2

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryInteractionMatching
end
