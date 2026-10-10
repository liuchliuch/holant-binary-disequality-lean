import Holant.Pauli.ExoticKlein.EightPortSetup

/-! Exact contractions of the specified original port pairs (3,5) and (4,5).
All fusion multipliers and the Frobenius-dual factor 1/2 are preserved. -/
namespace Holant.Pauli.ExoticKlein.EightPort
noncomputable section
open scoped BigOperators
open ProjectiveDetermination

private theorem local45 (a b : Label) (x y : Bool) :
    (∑ u : Bool, ∑ v : Bool, dual 0 u v * E a x u * E b v y) =
      (1/2 : ℂ) * omega a b * E (a+b) x y := by
  have hf := congrFun (congrFun (fusion a b) x) y
  simp only [Kernel.mul_apply,scale] at hf
  simp only [Fintype.sum_bool,dual_apply,d_zero,theta_zero,E_zero]
  norm_num
  calc
    _ = (1/2 : ℂ) * (E a x false * E b false y + E a x true * E b true y) := by ring
    _ = _ := by rw [hf]; ring

private theorem local35 (a b : Label) (x y : Bool) :
    (∑ u : Bool, ∑ v : Bool, dual 0 u v * E a u x * E b v y) =
      (1/2 : ℂ) * transposeScalar a * omega (theta a) b * E (theta a+b) x y := by
  have ht (u : Bool) : E a u x = transposeScalar a * E (theta a) x u := by
    exact congrFun (congrFun (transpose_E a) x) u
  simp_rw [ht]
  calc
    _ = transposeScalar a * (∑ u : Bool, ∑ v : Bool,
        dual 0 u v * E (theta a) x u * E b v y) := by
      norm_num [Fintype.sum_bool]
      ring
    _ = _ := by rw [local45]; ring

/-- Two-port contraction commutes with the finite label expansion. -/
theorem pairCard_sum (r s : Fin 8) (a : Label) (F : Label → Signature ℂ 8) :
    pairCard r s a (fun x => ∑ g, F g x) = fun z => ∑ g, pairCard r s a (F g) z := by
  funext z
  simp [pairCard,Finset.mul_sum,Finset.sum_add_distrib]

private theorem term35 (c : ℂ) (g a b d : Label) (z : Rest (2 : Fin 8) 4 → Bool) :
    pairCard 2 4 0 (fun x => c * E g (x 0) (x 1) * E a (x 2) (x 3) *
      E b (x 4) (x 5) * E d (x 6) (x 7)) z =
    c * (1/2 : ℂ) * transposeScalar a * omega (theta a) b *
      residual35.tensor ![g,theta a+b,d] z := by
  simp only [pairCard,residual35_tensor]
  simp only [fill]
  norm_num
  calc
    _ = c * E g (z ⟨0,by decide⟩) (z ⟨1,by decide⟩) *
        (∑ u : Bool, ∑ v : Bool, dual 0 u v *
          E a u (z ⟨3,by decide⟩) * E b v (z ⟨5,by decide⟩)) *
        E d (z ⟨6,by decide⟩) (z ⟨7,by decide⟩) := by
      norm_num [Fintype.sum_bool]
      ring
    _ = _ := by rw [local35]; ring

private theorem term45 (c : ℂ) (g a b d : Label) (z : Rest (3 : Fin 8) 4 → Bool) :
    pairCard 3 4 0 (fun x => c * E g (x 0) (x 1) * E a (x 2) (x 3) *
      E b (x 4) (x 5) * E d (x 6) (x 7)) z =
    c * (1/2 : ℂ) * omega a b * residual45.tensor ![g,a+b,d] z := by
  simp only [pairCard,residual45_tensor]
  simp only [fill]
  norm_num
  calc
    _ = c * E g (z ⟨0,by decide⟩) (z ⟨1,by decide⟩) *
        (∑ u : Bool, ∑ v : Bool, dual 0 u v *
          E a (z ⟨2,by decide⟩) u * E b v (z ⟨5,by decide⟩)) *
        E d (z ⟨6,by decide⟩) (z ⟨7,by decide⟩) := by
      norm_num [Fintype.sum_bool]
      ring
    _ = _ := by rw [local45]; ring

/-- Contracting original ports 3 and 5 creates the transpose-fusion label map. -/
theorem pairCard35_normalForm (lambda : Label → ℂ) (A1 A2 A3 : Label ≃+ Label) :
    pairCard 2 4 0 (normalForm lambda A1 A2 A3) =
      fun z => ∑ g, weight35 lambda A1 A2 g *
        residual35.tensor (labelTriple (D35 A1 A2) A3 g) z := by
  unfold normalForm
  rw [pairCard_sum]
  funext z
  apply Finset.sum_congr rfl
  intro g hg
  exact term35 (lambda g) g (A1 g) (A2 g) (A3 g) z

/-- Contracting original ports 4 and 5 creates the ordinary fusion label map. -/
theorem pairCard45_normalForm (lambda : Label → ℂ) (A1 A2 A3 : Label ≃+ Label) :
    pairCard 3 4 0 (normalForm lambda A1 A2 A3) =
      fun z => ∑ g, weight45 lambda A1 A2 g *
        residual45.tensor (labelTriple (D45 A1 A2) A3 g) z := by
  unfold normalForm
  rw [pairCard_sum]
  funext z
  apply Finset.sum_congr rfl
  intro g hg
  exact term45 (lambda g) g (A1 g) (A2 g) (A3 g) z

end
end Holant.Pauli.ExoticKlein.EightPort
