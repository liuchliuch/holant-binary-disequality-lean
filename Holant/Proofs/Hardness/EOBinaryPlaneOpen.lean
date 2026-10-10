import Holant.Proofs.Hardness.EOBinaryPlaneCore
import Holant.Network

/-! Exact one-bit-per-edge summation for arbitrary open native-X networks.
The two physical edge ends are independent before the X factor is summed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneOpen
open Holant
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
local instance : Fintype Bool := Bool.fintype

def assignments (E : ℕ) : ((Fin E×Bool)→Bool) ≃ ((Fin E→Bool)×(Fin E→Bool)) where
  toFun z := (fun e=>z (e,false),fun e=>z (e,true))
  invFun p e := if e.2 then p.2 e.1 else p.1 e.1
  left_inv := by intro z; funext e; rcases e with ⟨e,b⟩; cases b <;> rfl
  right_inv := by intro p; rcases p with ⟨a,b⟩; rfl

theorem edge_product {K : Type*} [CommSemiring K] {E : ℕ} (a b : Fin E→Bool) :
    (∏e,Signature.disequality (K:=K) (a e) (b e))=
      if b=(fun e=>!(a e)) then 1 else 0 := by
  classical
  by_cases h : b=(fun e=>!(a e))
  · rw [ite_eq_left h,h]
    apply Finset.prod_eq_one
    intro e _
    cases ha : a e <;> simp [Signature.disequality,ha]
  · rw [ite_eq_right h]
    have hh : ∃e,b e≠!(a e) := by simpa only [funext_iff,not_forall] using h
    obtain ⟨e,he⟩ := hh
    apply Finset.prod_eq_zero (Finset.mem_univ e)
    cases ha : a e <;> cases hb : b e <;> simp_all [Signature.disequality]

theorem native_sum {K : Type*} [CommSemiring K] {q : ℕ} (N : Network K q)
    (he : ∀e,N.edge e=Signature.disequality) (x : Fin q→Bool) :
    N.denote x=∑a : Fin N.shape.edges→Bool,∏v : Fin N.shape.vertices,
      N.vertex v (N.shape.assignment x (fun e=>if e.2 then !(a e.1) else a e.1) v) := by
  classical
  unfold Network.denote
  simp only [he]
  rw [←(assignments N.shape.edges).symm.sum_comp,Fintype.sum_prod_type]
  simp only [assignments,Equiv.coe_fn_symm_mk,Bool.false_eq_true,ite_false,ite_true,edge_product]
  simp only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneOpen
