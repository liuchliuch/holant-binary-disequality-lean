import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinHigherNonaffineCycleFamily

/-! Arbitrary oriented perfect matchings on a finite physical port set. The
port bijection enforces exact coverage and retains original endpoint order.
All coefficients are literal tensor contractions in this physical basis. -/
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffine
noncomputable section
open scoped BigOperators

structure Matching (P : Type*) (r : ℕ) where
  ports : (Fin r × Bool) ≃ P

namespace Matching
variable {P : Type*} {r : ℕ}

def assignmentEquiv (M : Matching P r) : (P → Bool) ≃ (Fin r → Bool × Bool) where
  toFun x e := (x (M.ports (e,false)),x (M.ports (e,true)))
  invFun y p := if (M.ports.symm p).2 then (y (M.ports.symm p).1).2 else (y (M.ports.symm p).1).1
  left_inv x := by
    funext p
    obtain ⟨⟨e,b⟩,rfl⟩ := M.ports.surjective p
    cases b <;> simp
  right_inv y := by
    funext e
    simp

def tensor (M : Matching P r) (labels : Fin r → Label) : Tensor ℂ P :=
  fun x => ∏ e, E (labels e) (x (M.ports (e,false))) (x (M.ports (e,true)))

def dualTensor (M : Matching P r) (labels : Fin r → Label) : Tensor ℂ P :=
  fun x => ∏ e, dual (labels e) (x (M.ports (e,false))) (x (M.ports (e,true)))

variable [Fintype P] [DecidableEq P]

def coefficient (M : Matching P r) (T : Tensor ℂ P) (labels : Fin r → Label) : ℂ :=
  ∑ x, M.dualTensor labels x*T x

def overlap (M N : Matching P r) (fixed labels : Fin r → Label) : ℂ := M.coefficient (N.tensor fixed) labels

theorem port_card (M : Matching P r) : Fintype.card P = 2*r := by
  have h := Fintype.card_congr M.ports
  simpa [mul_comm] using h.symm

theorem sum_assignments (M : Matching P r) (f : (P → Bool) → ℂ) :
    ∑ x, f x = ∑ y : Fin r → Bool × Bool, f (M.assignmentEquiv.symm y) :=
  Fintype.sum_equiv M.assignmentEquiv f (fun y => f (M.assignmentEquiv.symm y))
    (fun x => congrArg f (M.assignmentEquiv.symm_apply_apply x).symm)

@[simp] theorem tensor_coordinates (M : Matching P r) (labels : Fin r → Label) (y : Fin r → Bool × Bool) :
    M.tensor labels (M.assignmentEquiv.symm y) = ∏ e, E (labels e) (y e).1 (y e).2 := by
  simp [tensor,assignmentEquiv]

@[simp] theorem dual_coordinates (M : Matching P r) (labels : Fin r → Label) (y : Fin r → Bool × Bool) :
    M.dualTensor labels (M.assignmentEquiv.symm y) = ∏ e, dual (labels e) (y e).1 (y e).2 := by
  simp [dualTensor,assignmentEquiv]

private theorem prod_delta {A : Type*} [DecidableEq A] (x y : Fin r → A) :
    (∏ i, if x i = y i then (1 : ℂ) else 0) = if x = y then 1 else 0 := by
  classical
  by_cases h : x = y
  · subst y; simp
  · rw [if_neg h]
    obtain ⟨i,hi⟩ : ∃ i, x i ≠ y i := by
      by_contra hn
      push_neg at hn
      exact h (funext hn)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

/-- The M-dual product is exactly dual to the M-product basis, even for r=0. -/
theorem same_matching_coefficient (M : Matching P r) (a b : Fin r → Label) :
    M.coefficient (M.tensor b) a = if a = b then 1 else 0 := by
  classical
  unfold coefficient
  rw [M.sum_assignments]
  simp only [tensor_coordinates,dual_coordinates,← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (i : Fin r) (p : Bool × Bool) => dual (a i) p.1 p.2*E (b i) p.1 p.2)]
  have hlocal (i : Fin r) :
      (∑ p : Bool × Bool, dual (a i) p.1 p.2*E (b i) p.1 p.2) = if a i = b i then 1 else 0 := by
    simpa only [Fintype.sum_prod_type,Kernel.pair] using dual_pair (a i) (b i)
  simp_rw [hlocal]
  exact prod_delta a b

private theorem local_complete (x y : Bool × Bool) :
    ∑ a : Label, dual a x.1 x.2*E a y.1 y.2 = if x = y then 1 else 0 := by
  have h := dual_complete y.1 y.2 x.1 x.2
  have he : (y.1 = x.1 ∧ y.2 = x.2) ↔ x = y := by
    constructor
    · rintro ⟨h0,h1⟩; exact Prod.ext h0.symm h1.symm
    · rintro rfl; simp
  simpa only [he,mul_comm] using h

/-- Full tensor tomography for every actual oriented perfect matching. -/
theorem expansion (M : Matching P r) (T : Tensor ℂ P) (x : P → Bool) :
    ∑ labels : Fin r → Label, M.coefficient T labels*M.tensor labels x = T x := by
  classical
  let y₀ := M.assignmentEquiv x
  have hx : M.assignmentEquiv.symm y₀ = x := M.assignmentEquiv.symm_apply_apply x
  unfold coefficient
  simp_rw [M.sum_assignments]
  simp only [dual_coordinates]
  rw [← hx]
  simp only [tensor_coordinates,Finset.sum_mul]
  rw [Finset.sum_comm]
  calc
    (∑ y : Fin r → Bool × Bool, ∑ labels : Fin r → Label,
      ((∏ e, dual (labels e) (y e).1 (y e).2)*T (M.assignmentEquiv.symm y)) *
        ∏ e, E (labels e) (y₀ e).1 (y₀ e).2) =
      ∑ y : Fin r → Bool × Bool, T (M.assignmentEquiv.symm y)*
        ∏ e, ∑ a : Label, dual a (y e).1 (y e).2*E a (y₀ e).1 (y₀ e).2 := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [Fintype.prod_sum,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro labels hl
      rw [Finset.prod_mul_distrib]
      ring
    _ = ∑ y : Fin r → Bool × Bool, T (M.assignmentEquiv.symm y)*(if y = y₀ then 1 else 0) := by
      simp_rw [local_complete,prod_delta]
    _ = T (M.assignmentEquiv.symm y₀) := by simp

/-- The basis coefficients of any linear combination are its supplied scalars;
combined with expansion this proves faithful basis coordinates. -/
theorem coefficient_expansion (M : Matching P r) (c : (Fin r → Label) → ℂ) (a : Fin r → Label) :
    M.coefficient (fun x => ∑ b, c b*M.tensor b x) a = c a := by
  classical
  unfold coefficient
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    (∑ b, ∑ x, M.dualTensor a x*(c b*M.tensor b x)) =
        ∑ b, c b*M.coefficient (M.tensor b) a := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [coefficient,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      ring
    _ = c a := by simp only [same_matching_coefficient]; simp

end Matching
end
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffine
