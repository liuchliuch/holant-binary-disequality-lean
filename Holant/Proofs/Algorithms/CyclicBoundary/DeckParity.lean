import Holant.Projective.CyclicQuaternary.PhysicalSource


namespace Holant.LocalDrafts.MainChain.CyclicBoundary.DeckParity
open Holant.Projective.CyclicQuaternary Holant.Projective.CyclicPhasePencil
noncomputable section
variable {K : Type*} [Field K] [CharZero K]

theorem phase_offDiagonal {N : ℕ} {T : Kernel K}
    (h : T=0 ∨ IsPhase N T) (u v : Bool) (huv : u ≠ v) : T u v=0 := by
  rcases h with rfl | ⟨s,c,hs,hc,rfl⟩
  · rfl
  · simp [phase,diagonal,huv]

theorem contraction_offDiagonal {N : ℕ} {q : Signature K 4}
    (h : AllPhaseCards N q) (i : Fin 3) (side : Bool) (s : K) (hs : s^N=1)
    (u v : Bool) (huv : u ≠ v) : contraction q i side s u v=0 := by
  have hz := phase_offDiagonal (h i side false s hs) u v huv
  cases u <;> cases v <;>
    simp_all [transferCard,orderedContraction,Kernel.mul,Z,diagonal]

/-- These are the two individual original coefficients, not merely their
sum. Characteristic zero makes the two actual phase equations independent. -/
theorem zero_slices {N : ℕ} (hN : Even N) {q : Signature K 4}
    (h : AllPhaseCards N q) (i : Fin 3) (side : Bool)
    (u v : Bool) (huv : u ≠ v) :
    q (join i side false false u v)=0 ∧ q (join i side true true u v)=0 := by
  have hplus := contraction_offDiagonal h i side 1 (one_pow N) u v huv
  have hminus := contraction_offDiagonal h i side (-1) (by simp [hN.neg_pow]) u v huv
  rw [contraction_two_terms] at hplus hminus
  constructor
  · linear_combination (hplus+hminus)/2
  · linear_combination (hminus-hplus)/2

theorem even_of_cyclic_deck {N : ℕ} (hN : Even N) {q : Signature K 4}
    (h : AllPhaseCards N q) : EvenSupported q := by
  have hz (i : Fin 3) (side a u v : Bool) (huv : u ≠ v) :
      q (join i side a a u v)=0 := by
    cases a
    · exact (zero_slices hN h i side u v huv).1
    · exact (zero_slices hN h i side u v huv).2
  intro w hw
  have hw' : w=![w 0,w 1,w 2,w 3] := by funext j; fin_cases j <;> rfl
  rw [hw']
  cases h0 : w 0 <;> cases h1 : w 1 <;> cases h2 : w 2 <;> cases h3 : w 3 <;>
    simp only [odd,h0,h1,h2,h3,Bool.xor_false,Bool.xor_true,Bool.not_false,Bool.not_true] at hw
  all_goals first
    | contradiction
    | simpa [join] using hz 0 false false false true (by decide)
    | simpa [join] using hz 0 false false true false (by decide)
    | simpa [join] using hz 1 false false true false (by decide)
    | simpa [join] using hz 0 true false true false (by decide)
    | simpa [join] using hz 0 false true true false (by decide)
    | simpa [join] using hz 0 false true false true (by decide)
    | simpa [join] using hz 1 false true false true (by decide)
    | simpa [join] using hz 0 true true false true (by decide)

/-- Existing source-family classification can now be called without adding
the parity condition that 7.4 itself is required to establish. -/
theorem physical_even {F : SignatureFamily Holant.Tractable.AlgebraicComplex}
    {N : ℕ} (R : Physical.Representatives F N) (hN : Even N)
    (q : Signature Holant.Tractable.AlgebraicComplex 4)
    (hcards : Physical.PhysicalCards R q) : EvenSupported (Physical.walsh q) :=
  even_of_cyclic_deck hN ((Physical.physicalCards_iff R q).mp hcards)

end
end Holant.LocalDrafts.MainChain.CyclicBoundary.DeckParity
