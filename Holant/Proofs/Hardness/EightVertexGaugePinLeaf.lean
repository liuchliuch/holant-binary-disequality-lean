import Holant.Proofs.Hardness.EightVertexGaugeParity
import Holant.Proofs.FiniteGroups.Stabilization.FactorWorklist

/-! Exact support inheritance through the saved factor tree. A one-hot
binary's retained unary leaf is a computational pin with its original
nonzero scalar. This assertion does not grant access outside that tree. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EightVertexGaugePinLeaf
open Holant Holant.LocalDrafts.FinitePGL2.Stabilization
open EightVertexGaugeParity
variable {K : Type*} [Field K]

def SingleSupport {n : ℕ} (f : Signature K n) : Prop :=
  ∃ x, f x ≠ 0 ∧ ∀ y, f y ≠ 0 → y = x

theorem split_left {f a b : AnySignature K} (s : ProperSplit f a b)
    (single : SingleSupport f.2) : SingleSupport a.2 := by
  obtain ⟨x,hx,unique⟩ := single
  have nonzero : (s.scale : K) *
      (a.2 (fun i => x (s.ports (.inl i))) * b.2 (fun i => x (s.ports (.inr i)))) ≠ 0 := by
    simpa only [← congrFun s.equation x] using hx
  have parts := mul_ne_zero_iff.mp (mul_ne_zero_iff.mp nonzero).2
  refine ⟨(fun i => x (s.ports (.inl i))),parts.1,?_⟩
  intro y hy
  let z := fun i => Sum.elim y (fun j => x (s.ports (.inr j))) (s.ports.symm i)
  have hz : f.2 z ≠ 0 := by
    rw [s.equation]
    simpa only [z,Equiv.symm_apply_apply,Sum.elim_inl,Sum.elim_inr] using
      mul_ne_zero s.scale.ne_zero (mul_ne_zero hy parts.2)
  have equal := unique z hz
  funext i
  simpa only [z,Equiv.symm_apply_apply,Sum.elim_inl] using congrFun equal (s.ports (.inl i))

theorem split_right {f a b : AnySignature K} (s : ProperSplit f a b)
    (single : SingleSupport f.2) : SingleSupport b.2 := by
  obtain ⟨x,hx,unique⟩ := single
  have nonzero : (s.scale : K) *
      (a.2 (fun i => x (s.ports (.inl i))) * b.2 (fun i => x (s.ports (.inr i)))) ≠ 0 := by
    simpa only [← congrFun s.equation x] using hx
  have parts := mul_ne_zero_iff.mp (mul_ne_zero_iff.mp nonzero).2
  refine ⟨(fun i => x (s.ports (.inr i))),parts.2,?_⟩
  intro y hy
  let z := fun i => Sum.elim (fun j => x (s.ports (.inl j))) y (s.ports.symm i)
  have hz : f.2 z ≠ 0 := by
    rw [s.equation]
    simpa only [z,Equiv.symm_apply_apply,Sum.elim_inl,Sum.elim_inr] using
      mul_ne_zero s.scale.ne_zero (mul_ne_zero parts.1 hy)
  have equal := unique z hz
  funext i
  simpa only [z,Equiv.symm_apply_apply,Sum.elim_inr] using congrFun equal (s.ports (.inr i))

theorem leaf_support {f : AnySignature K} (tree : FactorTree f)
    (single : SingleSupport f.2) (g : AnySignature K) (member : g ∈ tree.leaves) :
    SingleSupport g.2 := by
  induction tree with
  | leaf f prime =>
    have equal : g = f := Multiset.mem_singleton.mp member
    subst g
    exact single
  | split split left right ihl ihr =>
    rcases Multiset.mem_add.mp member with leftMem | rightMem
    · exact ihl (split_left split single) leftMem
    · exact ihr (split_right split single) rightMem

theorem binary_support (B : Bool → Bool → K) (hot : OneHot B) :
    SingleSupport (fun x : Fin 2 → Bool => B (x 0) (x 1)) := by
  obtain ⟨a,b,live,zero⟩ := hot
  refine ⟨![a,b],live,?_⟩
  intro y hy
  have h0 : y 0 = a := by
    by_contra h
    exact hy (zero (y 0) (y 1) (Or.inl h))
  have h1 : y 1 = b := by
    by_contra h
    exact hy (zero (y 0) (y 1) (Or.inr h))
  funext i
  fin_cases i <;> assumption

/-- Original scalar, literal computational bit, and zero other entry. -/
theorem unary_formula (u : Signature K 1) (single : SingleSupport u) :
    ∃ b c, c ≠ 0 ∧ u = fun x => if x 0 = b then c else 0 := by
  classical
  obtain ⟨x,live,unique⟩ := single
  refine ⟨x 0,u x,live,?_⟩
  funext y
  by_cases same : y 0 = x 0
  · have equal : y = x := by
      funext i
      have hi : i = 0 := Fin.eq_zero i
      simpa only [hi] using same
    simp [equal]
  · rw [ite_eq_right same]
    by_contra nonzero
    exact same (congrFun (unique y nonzero) 0)

theorem unary_native_isotropic (u : Signature K 1) (single : SingleSupport u) :
    Signature.connect Signature.disequality
      (fun b => u (fun _ => b)) (fun b => u (fun _ => b)) = 0 := by
  obtain ⟨b,c,_,equal⟩ := unary_formula u single
  rw [equal,Signature.connect_disequality]
  cases b <;> simp

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EightVertexGaugePinLeaf
end
