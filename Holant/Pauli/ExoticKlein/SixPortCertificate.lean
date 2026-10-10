import Holant.Pauli.ExoticKlein.SixPortLinearCertificate

/-! A sound finite branching certificate for homogeneous scale elimination.
Every target line is branched on, including its zero output. Row reductions
are checked by exact Q(i) linear-combination witnesses. No numerical scale
sampling, rank oracle, or liveness approximation is used. -/
namespace Holant.Pauli.ExoticKlein.SixPort.LinearCertificate
noncomputable section

structure Problem (n m q d k t : ℕ) where
  tensor : Fin m → Row n
  cards : Fin d → Fin q → Row n
  cardLines : Fin k → Fin q → Q
  cardPivot : Fin k → Fin q
  targets : Fin t → Fin m → Q
  targetPivot : Fin t → Fin m
  live : Fin n → Bool

namespace Problem
variable {n m q d k t : ℕ}

def Live (problem : Problem n m q d k t) (scale : Fin n → ℂ) : Prop :=
  ∀ i, problem.live i = true → scale i ≠ 0

/-- A zero card is included by choosing scalar zero. -/
def SafeCards (problem : Problem n m q d k t) (scale : Fin n → ℂ) : Prop :=
  ∀ c, ∃ j, ∃ s : ℂ, ∀ i,
    output (problem.cards c) scale i = s*Algebraic.gaussianToComplex (problem.cardLines j i)

def Accepted (problem : Problem n m q d k t) (scale : Fin n → ℂ) : Prop :=
  ∃ j, ∃ s : ℂ, ∀ i,
    output problem.tensor scale i = s*Algebraic.gaussianToComplex (problem.targets j i)

end Problem

inductive Certificate (n m d k t : ℕ) where
  | dead : Fin n → List Q → Certificate n m d k t
  | product : Fin t → (Fin m → List Q) → Certificate n m d k t
  | split : Fin d → (Fin k → Reduction n) → (Fin k → Certificate n m d k t) → Certificate n m d k t

namespace Certificate
variable {n m q d k t : ℕ}

/-- Every Boolean test here is exact rational arithmetic. The semantic tensor
and its contractions are supplied as literal matrices by the concrete problem. -/
def check (problem : Problem n m q d k t) (rows : List (Row n)) : Certificate n m d k t → Bool
  | .dead i weights => problem.live i && CheckRow rows (unitRow i) weights
  | .product j weights => decide (problem.targets j (problem.targetPivot j) ≠ 0) &&
      decide (∀ i : Fin m, CheckRow rows
        (wedgeRow problem.tensor (problem.targets j) (problem.targetPivot j) i) (weights i) = true)
  | .split c reductions children =>
      decide (∀ j : Fin k,
        (reductions j).check (rows++wedgeRows (problem.cards c) (problem.cardLines j) (problem.cardPivot j)) = true ∧
        check problem (reductions j).rows (children j) = true)

/-- Kernel-checkable certificate soundness for all complex scales, including
every cancellation locus. A certificate cannot discard a branch merely because
some output is zero: zero belongs to every target-line preimage. -/
theorem sound (problem : Problem n m q d k t) (certificate : Certificate n m d k t) :
    ∀ rows, check problem rows certificate = true → ∀ scale : Fin n → ℂ,
      Satisfies rows scale → problem.Live scale → problem.SafeCards scale → problem.Accepted scale := by
  induction certificate with
  | dead i weights =>
    intro rows hc scale hrows hlive hsafe
    have hh : problem.live i = true ∧ CheckRow rows (unitRow i) weights = true := Bool.and_eq_true_iff.mp hc
    have hi := checked_row_sound rows (unitRow i) weights hh.2 hrows
    rw [evaluate_unitRow] at hi
    exact False.elim (hlive i hh.1 hi)
  | product j weights =>
    intro rows hc scale hrows hlive hsafe
    have hh : decide (problem.targets j (problem.targetPivot j) ≠ 0) = true ∧
        decide (∀ i : Fin m, CheckRow rows
          (wedgeRow problem.tensor (problem.targets j) (problem.targetPivot j) i) (weights i) = true) = true :=
      Bool.and_eq_true_iff.mp hc
    have hp : problem.targets j (problem.targetPivot j) ≠ 0 := of_decide_eq_true hh.1
    have hall : ∀ i : Fin m, CheckRow rows
        (wedgeRow problem.tensor (problem.targets j) (problem.targetPivot j) i) (weights i) = true :=
      of_decide_eq_true hh.2
    have hs : Satisfies (wedgeRows problem.tensor (problem.targets j) (problem.targetPivot j)) scale := by
      rw [satisfies_wedgeRows_iff]
      intro i
      exact checked_row_sound rows _ _ (hall i) hrows
    obtain ⟨s,he⟩ := wedgeRows_implies_line problem.tensor (problem.targets j) (problem.targetPivot j) hp scale hs
    exact ⟨j,s,he⟩
  | split c reductions children ih =>
    intro rows hc scale hrows hlive hsafe
    have hall : ∀ j : Fin k,
        (reductions j).check (rows++wedgeRows (problem.cards c) (problem.cardLines j) (problem.cardPivot j)) = true ∧
        check problem (reductions j).rows (children j) = true := of_decide_eq_true hc
    obtain ⟨j,s,he⟩ := hsafe c
    have hadded : Satisfies (rows++wedgeRows (problem.cards c) (problem.cardLines j) (problem.cardPivot j)) scale :=
      (satisfies_append _ _ _).mpr ⟨hrows,line_implies_wedgeRows _ _ _ _ s he⟩
    have hnext := (reductions j).sound _ (hall j).1 hadded
    exact ih j _ (hall j).2 scale hnext hlive hsafe

end Certificate
end
end Holant.Pauli.ExoticKlein.SixPort.LinearCertificate
