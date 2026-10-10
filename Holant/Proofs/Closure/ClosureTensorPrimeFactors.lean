import Holant.Proofs.FiniteGroups.Stabilization.FactorWorklist
import Holant.Tensor

/-! Actual analytic tensor factors contradict the retained all-arity Prime
predicate, with the exact ordered port bijection and unit multiplier retained.
This is a mathematical local factor consumer, not a hardness/evaluator oracle. -/
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureTensorPrimeFactors
open Holant Holant.LocalDrafts.FinitePGL2.Stabilization
variable {K : Type*} [Field K] {m n k : ℕ}

def splitOfTensor (f : Signature K k) (left : Signature K m) (right : Signature K n)
    (ports : (Fin m ⊕ Fin n) ≃ Fin k) (leftPos : 0 < m) (rightPos : 0 < n)
    (equation : f = Tensor.reindex ports (Tensor.tensor left right)) :
    ProperSplit (⟨k,f⟩ : AnySignature K) ⟨m,left⟩ ⟨n,right⟩ where
  left_pos := leftPos
  right_pos := rightPos
  ports := ports
  scale := 1
  equation := by
    funext x
    exact (congrFun equation x).trans (one_mul _).symm

theorem prime_not_tensor (f : Signature K k) (prime : Prime (⟨k,f⟩ : AnySignature K))
    (left : Signature K m) (right : Signature K n)
    (ports : (Fin m ⊕ Fin n) ≃ Fin k) (leftPos : 0 < m) (rightPos : 0 < n) :
    f ≠ Tensor.reindex ports (Tensor.tensor left right) := by
  intro equation
  exact prime.2 ⟨⟨m,left⟩,⟨n,right⟩,⟨splitOfTensor f left right ports leftPos rightPos equation⟩⟩

/-- No assumption that a selected analytic factor is gadget-realizable is
needed to refute primality. Physical factor access remains a separate boundary. -/
theorem prime_excludes_nonempty_tensor_factor (f : Signature K k)
    (prime : Prime (⟨k,f⟩ : AnySignature K)) :
    ¬ ∃ (m n : ℕ) (_ : 0 < m) (_ : 0 < n)
      (ports : (Fin m ⊕ Fin n) ≃ Fin k) (left : Signature K m) (right : Signature K n),
      f = Tensor.reindex ports (Tensor.tensor left right) := by
  rintro ⟨m,n,hm,hn,ports,left,right,equation⟩
  exact prime_not_tensor f prime left right ports hm hn equation

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureTensorPrimeFactors
