import Holant.Certificates.EqualityQuaternary.Primality

/-! Arbitrary independent invertible port actions preserve genuine tensor
primality. The proof transports factors through the original port cut.
-/
noncomputable section
namespace Holant.Certificates.EqualityQuaternary
open Holant Holant.Marked Holant.Tractable
set_option backward.isDefEq.respectTransparency false

def splitAssignments {m n : ℕ} (p : (Fin m ⊕ Fin n) ≃ Fin 4) :
    (Fin 4 → Bool) ≃ ((Fin m → Bool) × (Fin n → Bool)) :=
  (Equiv.arrowCongr p.symm (Equiv.refl Bool)).trans
    (Equiv.sumArrowEquivProdArrow (Fin m) (Fin n) Bool)

theorem coordinateAction_split {m n : ℕ} (p : (Fin m ⊕ Fin n) ≃ Fin 4)
    (A : Fin 4 → Mat) (f : Signature Scalar m) (g : Signature Scalar n) :
    Signature.coordinateAction A (Tensor.reindex p (Tensor.tensor f g))=
      Tensor.reindex p (Tensor.tensor
        (Signature.coordinateAction (fun j => A (p (.inl j))) f)
        (Signature.coordinateAction (fun j => A (p (.inr j))) g)) := by
  classical
  funext x
  simp only [Signature.coordinateAction,Tensor.reindex,Tensor.tensor]
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [←Fintype.sum_prod_type']
  apply Fintype.sum_equiv (splitAssignments p)
  intro y
  have hp : (∏ i : Fin 4,A i (x i) (y i)) =
      (∏ j : Fin m,A (p (.inl j)) (x (p (.inl j))) (y (p (.inl j)))) *
      (∏ j : Fin n,A (p (.inr j)) (x (p (.inr j))) (y (p (.inr j)))) := by
    rw [←p.prod_comp (fun i => A i (x i) (y i)),Fintype.prod_sum_type]
  change (∏ i,A i (x i) (y i)) *
      (f (fun j => y (p (.inl j)))*g (fun j => y (p (.inr j)))) =
    ((∏ j,A (p (.inl j)) (x (p (.inl j))) (y (p (.inl j)))) * f (fun j => y (p (.inl j)))) *
      ((∏ j,A (p (.inr j)) (x (p (.inr j))) (y (p (.inr j)))) * g (fun j => y (p (.inr j))))
  rw [hp]
  ring

theorem proper_coordinateAction {q : Signature Scalar 4} (h : ProperFactor q) (A : Fin 4 → Mat) :
    ProperFactor (Signature.coordinateAction A q) := by
  obtain ⟨m,n,hm,hn,p,f,g,hq⟩ := h
  refine ⟨m,n,hm,hn,p,Signature.coordinateAction (fun j => A (p (.inl j))) f,
    Signature.coordinateAction (fun j => A (p (.inr j))) g,?_⟩
  rw [hq,coordinateAction_split]

theorem prime_coordinateAction {q : Signature Scalar 4} (h : TensorPrime q)
    (A B : Fin 4 → Mat) (hinv : ∀ i,Kernel.mul (B i) (A i)=Signature.equality) :
    TensorPrime (Signature.coordinateAction A q) := by
  constructor
  · intro hz
    have hh := congrArg (Signature.coordinateAction B) hz
    rw [Signature.coordinateAction_cancel B A hinv,Signature.coordinateAction_zero] at hh
    exact h.1 hh
  · intro hf
    have hh := proper_coordinateAction hf B
    rw [Signature.coordinateAction_cancel B A hinv] at hh
    exact h.2 hh

theorem proper_smul {q : Signature Scalar 4} (h : ProperFactor q) (c : Scalar) : ProperFactor (c • q) := by
  obtain ⟨m,n,hm,hn,p,f,g,hq⟩ := h
  refine ⟨m,n,hm,hn,p,c • f,g,?_⟩
  funext x
  rw [hq]
  simp [Tensor.reindex,Tensor.tensor,mul_assoc]

theorem prime_smul {q : Signature Scalar 4} (h : TensorPrime q) (c : Scalar) (hc : c≠0) : TensorPrime (c • q) := by
  constructor
  · simpa [smul_eq_zero,hc] using h.1
  · intro hf
    have hh := proper_smul hf c⁻¹
    rw [smul_smul,inv_mul_cancel₀ hc,one_smul] at hh
    exact h.2 hh

end Holant.Certificates.EqualityQuaternary
