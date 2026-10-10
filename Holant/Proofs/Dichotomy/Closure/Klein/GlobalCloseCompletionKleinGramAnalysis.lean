import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinH8Table
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! Elementary real Gram consequences needed by the Pauli norm test.
Zero Gram diagonals force zero rows. Vanishing Gram minors force a literal
rank-one factorization of the original coefficient matrix, by an exact
sum-of-squares argument. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinGramAnalysis
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {I J : Type*} [Fintype J]

def gram (A : I→J→ℝ) (i k : I) : ℝ := ∑j,A i j*A k j

theorem symmetric (A : I→J→ℝ) (i k : I) : gram A i k=gram A k i := by
  simp only [gram,mul_comm]

theorem diagonal_nonnegative (A : I→J→ℝ) (i : I) : 0≤gram A i i :=
  Finset.sum_nonneg (fun j _=>mul_self_nonneg (A i j))

theorem zero_diagonal (A : I→J→ℝ) (i : I) (zero : gram A i i=0) : ∀j,A i j=0 := by
  have h : ∑j,A i j^2=0 := by simpa only [pow_two,gram] using zero
  exact fun j=>((Finset.sum_sq_eq_zero_iff Finset.univ (fun j=>A i j)).mp h) j (Finset.mem_univ _)

theorem zero_row (A : I→J→ℝ) (i : I) (zero : gram A i i=0) : ∀k,gram A i k=0 := by
  intro k
  simp [gram,zero_diagonal A i zero]

theorem positive_diagonal (A : I→J→ℝ) (i : I) (j : J) (nonzero : A i j≠0) : 0<gram A i i := by
  have nonnegative := diagonal_nonnegative A i
  have live : gram A i i≠0 := fun zero=>nonzero (zero_diagonal A i zero j)
  exact lt_of_le_of_ne nonnegative (Ne.symm live)

theorem factor_of_minors (A : I→J→ℝ) (i₀ : I) (j₀ : J) (nonzero : A i₀ j₀≠0)
    (minors : ∀i k,gram A i k*gram A i₀ i₀=gram A i i₀*gram A k i₀) :
    ∃u : I→ℝ,∃v : J→ℝ,∀i j,A i j=u i*v j := by
  let d := gram A i₀ i₀
  have hd : d≠0 := ne_of_gt (positive_diagonal A i₀ j₀ nonzero)
  let u : I→ℝ := fun i=>gram A i i₀/d
  refine ⟨u,A i₀,?_⟩
  intro i j
  have square_zero : ∑k,(A i k-u i*A i₀ k)^2=0 := by
    have term (k : J) : (A i k-u i*A i₀ k)^2=
        A i k*A i k-(2*u i)*(A i k*A i₀ k)+(u i)^2*(A i₀ k*A i₀ k) := by ring
    simp_rw [term]
    simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.mul_sum]
    change gram A i i-(2*u i)*gram A i i₀+(u i)^2*d=0
    dsimp only [u]
    have h := minors i i
    change gram A i i*d=gram A i i₀*gram A i i₀ at h
    field_simp [hd]
    nlinarith
  have h := ((Finset.sum_sq_eq_zero_iff Finset.univ (fun k=>A i k-u i*A i₀ k)).mp square_zero) j (Finset.mem_univ _)
  exact sub_eq_zero.mp h


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinGramAnalysis
end
