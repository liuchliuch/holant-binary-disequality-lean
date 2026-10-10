import Holant.Dihedral.EndpointParallelogram.Linear
import Mathlib.Data.Fintype.Pi
import Mathlib.LinearAlgebra.Pi

/-! Perfect matchings are recovered from their literal binary direction codes;
no equality of ordered edge lists is inferred from an arbitrary enumeration. -/
namespace Holant.Dihedral.EndpointParallelogram

variable {ι : Type*}

structure Pairing (ι : Type*) where
  mate : ι → ι
  involutive : Function.Involutive mate
  fixed_free : ∀ i, mate i ≠ i

namespace Pairing

@[ext] theorem ext {M N : Pairing ι} (h : M.mate = N.mate) : M = N := by
  cases M
  cases N
  cases h
  rfl

def code (M : Pairing ι) : Submodule (ZMod 2) (ι → ZMod 2) where
  carrier := {x | ∀ i, x (M.mate i) = x i}
  zero_mem' := by intro i; rfl
  add_mem' := by intro x y hx hy i; simp only [Pi.add_apply,hx i,hy i]
  smul_mem' := by intro c x hx i; simp only [Pi.smul_apply,hx i]

@[simp] theorem mem_code (M : Pairing ι) (x : ι → ZMod 2) :
    x ∈ M.code ↔ ∀ i, x (M.mate i) = x i := Iff.rfl

variable [DecidableEq ι]

/-- The weight-two indicator of one literal matched pair. -/
def edgeWord (M : Pairing ι) (i : ι) : ι → ZMod 2 :=
  fun j => if j = i ∨ j = M.mate i then 1 else 0

theorem edgeWord_mem (M : Pairing ι) (i : ι) : M.edgeWord i ∈ M.code := by
  intro j
  have h₁ : M.mate j = i ↔ j = M.mate i := by
    constructor
    · intro h
      simpa only [M.involutive j] using congrArg M.mate h
    · rintro rfl
      exact M.involutive i
  have h₂ : M.mate j = M.mate i ↔ j = i := M.involutive.injective.eq_iff
  simp only [edgeWord,h₁,h₂,or_comm]

/-- A perfect matching is determined by its weight-two indicator words. -/
theorem code_injective : Function.Injective (code (ι := ι)) := by
  intro M N h
  apply Pairing.ext
  funext i
  have hm : M.edgeWord i ∈ N.code := h ▸ M.edgeWord_mem i
  have hh := hm i
  have hi : M.edgeWord i i = 1 := by simp [edgeWord]
  rw [hi] at hh
  have hj : N.mate i = i ∨ N.mate i = M.mate i := by
    by_contra hn
    simp [edgeWord,hn] at hh
  exact (hj.resolve_left (N.fixed_free i)).symm

theorem code_eq_iff (M N : Pairing ι) : M.code = N.code ↔ M = N :=
  ⟨fun h => code_injective h,congrArg code⟩

end Pairing
end Holant.Dihedral.EndpointParallelogram
