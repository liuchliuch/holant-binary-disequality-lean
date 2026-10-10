import Holant.ReedMuller.DiagonalSlice.Integration

/-! The exact three-coordinate exception, with its common interaction scalar
computed from the original coefficient table. -/
namespace Holant.ReedMuller.DiagonalSlice
open scoped BigOperators
variable {G : Type*} [CommGroup G]

theorem integrate_three {h : Finset (Fin 3) → G} (h0 : h ∅ = 1)
    (hs : ∀ i j, i ≠ j → Simple h i j) :
    ∃ rho : Fin 3 → G, ∃ kappa : G,
      (∀ i, h {i} = rho i) ∧
      (∀ i j, i ≠ j → h {i,j} = kappa * rho i * rho j) ∧
      h Finset.univ = kappa * rho 0 * rho 1 * rho 2 := by
  let rho : Fin 3 → G := fun i => h {i}
  let kappa := h Finset.univ / (rho 0 * rho 1 * rho 2)
  have e01 : outside (0:Fin 3) 1 = {2} := by decide
  have e02 : outside (0:Fin 3) 2 = {1} := by decide
  have e12 : outside (1:Fin 3) 2 = {0} := by decide
  have H01 : h Finset.univ = h {0,1} * rho 2 := by
    simpa [e01,rho] using slice_formula h0 (by decide : (0:Fin 3)≠1)
      (hs 0 1 (by decide)) Finset.univ (by simp)
  have H02 : h Finset.univ = h {0,2} * rho 1 := by
    simpa [e02,rho] using slice_formula h0 (by decide : (0:Fin 3)≠2)
      (hs 0 2 (by decide)) Finset.univ (by simp)
  have H12 : h Finset.univ = h {1,2} * rho 0 := by
    simpa [e12,rho] using slice_formula h0 (by decide : (1:Fin 3)≠2)
      (hs 1 2 (by decide)) Finset.univ (by simp)
  have p01 : h {0,1} = kappa * rho 0 * rho 1 := by dsimp [kappa]; rw [H01]; simp [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc]
  have p02 : h {0,2} = kappa * rho 0 * rho 2 := by dsimp [kappa]; rw [H02]; simp [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc]
  have p12 : h {1,2} = kappa * rho 1 * rho 2 := by dsimp [kappa]; rw [H12]; simp [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc]
  refine ⟨rho,kappa,(fun _ => rfl),?_,?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp only [ne_eq,not_true_eq_false] at hij
    · exact p01
    · exact p02
    · change h {1,0} = kappa * rho 1 * rho 0
      rw [Finset.pair_comm (1:Fin 3) 0]
      simpa [mul_comm,mul_left_comm,mul_assoc] using p01
    · exact p12
    · change h {2,0} = kappa * rho 2 * rho 0
      rw [Finset.pair_comm (2:Fin 3) 0]
      simpa [mul_comm,mul_left_comm,mul_assoc] using p02
    · change h {2,1} = kappa * rho 2 * rho 1
      rw [Finset.pair_comm (2:Fin 3) 1]
      simpa [mul_comm,mul_left_comm,mul_assoc] using p12
  · dsimp [kappa]; simp [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc]

end Holant.ReedMuller.DiagonalSlice
