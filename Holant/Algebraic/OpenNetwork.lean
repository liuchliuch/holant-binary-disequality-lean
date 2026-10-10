import Holant.Realization
import Holant.Tractable.Scalars

/-! Algebraicity follows from the actual finite open-network sum, including
free-stub boundary corrections and both permitted wire kinds. -/
namespace Holant.Algebraic
open Holant.Tractable
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

theorem edgeKind_algebraic (W : EdgeKind) (a b : Bool) :
    W.value (K:=ℂ) a b∈AlgebraicComplex := by
  cases W <;> cases a <;> cases b <;>
    first | exact AlgebraicComplex.zero_mem | exact AlgebraicComplex.one_mem

theorem open_tensor_algebraic (N : OpenNetwork ℂ n)
    (hv : ∀v x,IsAlgebraic ℚ (N.vertex v x)) (x : Fin n → Bool) :
    IsAlgebraic ℚ (N.tensor x) := by
  classical
  have hw (z : OpenPorts N.shape.vertices N.shape.arity N.shape.free → Bool) :
      N.weight z∈AlgebraicComplex := by
    unfold OpenNetwork.weight
    apply AlgebraicComplex.mul_mem
    · exact AlgebraicComplex.prod_mem (fun v _ => (hv v _).isIntegral)
    · exact AlgebraicComplex.prod_mem (fun e _ => edgeKind_algebraic _ _ _)
  have hr (y : Fin n → Bool) : N.raw y∈AlgebraicComplex := by
    unfold OpenNetwork.raw
    apply AlgebraicComplex.sum_mem
    intro z _
    split_ifs
    · exact hw z
    · exact AlgebraicComplex.zero_mem
  have hb (j : Fin n) (a b : Bool) : N.boundaryKernel j a b∈AlgebraicComplex := by
    unfold OpenNetwork.boundaryKernel
    cases N.shape.boundary j with
    | inl p => exact edgeKind_algebraic .equality a b
    | inr f => exact edgeKind_algebraic _ a b
  have ht : N.tensor x∈AlgebraicComplex := by
    unfold OpenNetwork.tensor Signature.coordinateAction
    apply AlgebraicComplex.sum_mem
    intro y _
    exact AlgebraicComplex.mul_mem
      (AlgebraicComplex.prod_mem (fun j _ => hb j _ _)) (hr y)
  exact ht.isAlgebraic

theorem realized_algebraic {Λ : SignatureFamily ℂ} {q : Signature ℂ n}
    (halg : ∀t∈Λ,∀x,IsAlgebraic ℚ (t.2 x))
    (hq : Gadget.Realizes Λ .disequality q) (x : Fin n → Bool) :
    IsAlgebraic ℚ (q x) := by
  obtain ⟨N,hv,_,rfl⟩ := hq
  exact open_tensor_algebraic N (fun v => halg _ (hv v)) x

theorem projectively_realized_algebraic {Λ : SignatureFamily ℂ} {q : Signature ℂ n}
    (halg : ∀t∈Λ,∀x,IsAlgebraic ℚ (t.2 x)) (c : ℂ) (hc : c≠0)
    (hcalg : IsAlgebraic ℚ c) (hq : Gadget.Realizes Λ .disequality (c • q))
    (x : Fin n → Bool) : IsAlgebraic ℚ (q x) := by
  have hmul : c*q x∈AlgebraicComplex := (realized_algebraic halg hq x).isIntegral
  have hd := AlgebraicComplex.div_mem hmul hcalg.isIntegral
  rw [mul_div_cancel_left₀ (q x) hc] at hd
  exact hd.isAlgebraic
end
end Holant.Algebraic
