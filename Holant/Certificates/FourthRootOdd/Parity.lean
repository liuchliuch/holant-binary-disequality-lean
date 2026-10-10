import Holant.Certificates.FourthRootOdd.DenseData

namespace Holant.Certificates.FourthRootOdd
open Holant

theorem odd_boundary_forces_even_input : ∀ p : Fin 6, ∀ u v : Bool, ∀ x : Fin 4 → Bool,
    evenWord x=false → evenWord (insertPair p u v (firstHalf x))=true ∨
      evenWord (insertPair p (!u) (!v) (secondHalf x))=true := by decide

theorem twoCopy_even {K : Type*} [Semiring K] (f : Signature K 4)
    (hf : ∀ x,evenWord x=true → f x=0) (p : Fin 6) (x : Fin 4 → Bool)
    (hx : evenWord x=false) : twoCopyNative f p x=0 := by
  rw [twoCopyNative_eq]
  unfold twoCopy
  apply Finset.sum_eq_zero
  intro u _
  apply Finset.sum_eq_zero
  intro v _
  rcases odd_boundary_forces_even_input p u v x hx with h | h
  · rw [hf _ h,zero_mul]
  · rw [hf _ h,mul_zero]

theorem complexOdd_even_zero (s : TwelveLoops.State) (x : Fin 4 → Bool)
    (hx : evenWord x=true) : complexOdd s x=0 := by
  cases h₀ : x 0 <;> cases h₁ : x 1 <;> cases h₂ : x 2 <;> cases h₃ : x 3 <;>
    simp [evenWord,h₀,h₁,h₂,h₃] at hx ⊢ <;>
    simp [complexOdd,TwelveLoops.oddTable,h₀,h₁,h₂,h₃]

theorem complexOdd_twoCopy_even (s : TwelveLoops.State) (p : Fin 6) (x : Fin 4 → Bool)
    (hx : evenWord x=false) : twoCopyNative (complexOdd s) p x=0 :=
  twoCopy_even _ (complexOdd_even_zero s) p x hx

end Holant.Certificates.FourthRootOdd
