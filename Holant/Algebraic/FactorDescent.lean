import Holant.Tensor
import Mathlib.Algebra.Field.Basic
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Exact tensor-factor descent through a fixed coefficient field

A nonzero rank-one table over a base field can have a factorization displayed in
an extension field. A single nonzero entry gives row/column ratios in the original
field, with no field enlargement and no discarded scalar. This is the tensor-split
algebra needed by manuscript Lemma 2.23; it does not establish that lemma's gadget
reduction, group, or machine-time assertions.
-/

namespace Holant.Algebraic.FactorDescent

variable {L K I J : Type*} [Field L] [Field K]

/-- The first factor is normalized to one at the chosen pivot row. -/
def rowFactor (h : I → J → L) (i₀ : I) (j₀ : J) (i : I) : L :=
  h i j₀ / h i₀ j₀

/-- The entire pivot scale stays in the second factor. -/
def columnFactor (h : I → J → L) (i₀ : I) (j : J) : L := h i₀ j

/-- Rank-one over the extension forces the exact cross-product identity over the
original field. The embedding is injective because its domain is a field. -/
theorem cross_identity (φ : L →+* K) (h : I → J → L) (u : I → K) (v : J → K)
    (huv : ∀ i j, φ (h i j) = u i * v j) (i i₀ : I) (j j₀ : J) :
    h i j * h i₀ j₀ = h i j₀ * h i₀ j := by
  apply φ.injective
  simp only [map_mul, huv]
  ring

/-- Explicit normalized factors over the frozen base field reproduce every entry
of the original table exactly, including zero rows and zero columns. -/
theorem exact_factorization (φ : L →+* K) (h : I → J → L) (u : I → K) (v : J → K)
    (huv : ∀ i j, φ (h i j) = u i * v j) (i₀ : I) (j₀ : J)
    (hp : h i₀ j₀ ≠ 0) (i : I) (j : J) :
    h i j = rowFactor h i₀ j₀ i * columnFactor h i₀ j := by
  dsimp [rowFactor, columnFactor]
  apply (mul_right_inj' hp).mp
  field_simp
  simpa [mul_comm] using cross_identity φ h u v huv i i₀ j j₀

@[simp] theorem rowFactor_pivot (h : I → J → L) (i₀ : I) (j₀ : J)
    (hp : h i₀ j₀ ≠ 0) : rowFactor h i₀ j₀ i₀ = 1 := div_self hp

theorem factors_nonzero (h : I → J → L) (i₀ : I) (j₀ : J)
    (hp : h i₀ j₀ ≠ 0) :
    rowFactor h i₀ j₀ ≠ 0 ∧ columnFactor h i₀ ≠ 0 := by
  constructor
  · intro hz
    have he := congrFun hz i₀
    rw [rowFactor_pivot h i₀ j₀ hp] at he
    exact one_ne_zero he
  · intro hz
    exact hp (congrFun hz j₀)

/-- The ambient first factor differs from the descended one by one fixed nonzero
scalar. This is an equality, not only a support or projective correspondence. -/
theorem ambient_row_factor (φ : L →+* K) (h : I → J → L) (u : I → K) (v : J → K)
    (huv : ∀ i j, φ (h i j) = u i * v j) (i₀ : I) (j₀ : J)
    (hp : h i₀ j₀ ≠ 0) :
    u i₀ ≠ 0 ∧ ∀ i, u i = u i₀ * φ (rowFactor h i₀ j₀ i) := by
  have hp' : u i₀ * v j₀ ≠ 0 := by
    rw [← huv]
    exact (map_ne_zero φ).mpr hp
  obtain ⟨hu, hv⟩ := mul_ne_zero_iff.mp hp'
  refine ⟨hu, fun i => ?_⟩
  simp only [rowFactor, map_div₀, huv]
  field_simp

/-- A nonzero ambient split always descends. The nonzero pivot is derived from
nonzeroness rather than assumed as an extra restriction on the signature. -/
theorem exists_exact_factorization (φ : L →+* K) (h : I → J → L)
    (u : I → K) (v : J → K) (huv : ∀ i j, φ (h i j) = u i * v j)
    (hne : h ≠ 0) :
    ∃ (f : I → L) (g : J → L), f ≠ 0 ∧ g ≠ 0 ∧ ∀ i j, h i j = f i * g j := by
  classical
  have hp : ∃ i j, h i j ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hne (funext fun i => funext fun j => hn i j)
  obtain ⟨i₀, j₀, hp⟩ := hp
  exact ⟨rowFactor h i₀ j₀, columnFactor h i₀,
    (factors_nonzero h i₀ j₀ hp).1, (factors_nonzero h i₀ j₀ hp).2,
    exact_factorization φ h u v huv i₀ j₀ hp⟩

/-- A two-block Boolean tensor split over an extension descends to the base field
with its port sets and all coefficients unchanged. Empty blocks are allowed. -/
theorem tensor_descent {ι κ : Type*} (φ : L →+* K) (h : Tensor L (ι ⊕ κ))
    (u : Tensor K ι) (v : Tensor K κ)
    (huv : ∀ x, φ (h x) = Tensor.tensor u v x)
    (x₀ : ι → Bool) (y₀ : κ → Bool) (hp : h (Sum.elim x₀ y₀) ≠ 0) :
    let table := fun x y => h (Sum.elim x y)
    let f := rowFactor table x₀ y₀
    let g := columnFactor table x₀
    h = Tensor.tensor f g ∧ f x₀ = 1 ∧ g y₀ ≠ 0 := by
  dsimp only
  have hs (x : ι → Bool) (y : κ → Bool) :
      φ (h (Sum.elim x y)) = u x * v y := huv (Sum.elim x y)
  refine ⟨?_, rowFactor_pivot _ _ _ hp, hp⟩
  funext z
  have he := exact_factorization φ (fun x y => h (Sum.elim x y)) u v hs x₀ y₀ hp
    (fun i => z (.inl i)) (fun j => z (.inr j))
  change h z = _
  have hz : Sum.elim (fun i => z (.inl i)) (fun j => z (.inr j)) = z := by
    funext p
    cases p <;> rfl
  simpa only [hz, Tensor.tensor_apply] using he

end Holant.Algebraic.FactorDescent
