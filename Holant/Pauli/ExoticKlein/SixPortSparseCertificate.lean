import Holant.Pauli.ExoticKlein.SixPortSymmetryTransport

/-! Sparse exact row witnesses. Only explicitly listed rows are evaluated;
all witnesses still have their arbitrary-complex-scale meaning proved here. -/
namespace Holant.Pauli.ExoticKlein.SixPort
noncomputable section
open LinearCertificate
open scoped BigOperators
namespace SparseCertificate

abbrev Weights := List (ℕ × Q)

def combine {n : ℕ} (rows : List (Row n)) : Weights → Row n
  | [] => fun _ => 0
  | (j,c)::rest => fun i => c*(rows.getD j (fun _ => 0)) i + combine rows rest i

theorem satisfies_getD {n : ℕ} {rows : List (Row n)} {scale : Fin n → ℂ}
    (h : Satisfies rows scale) (j : ℕ) : evaluate (rows.getD j (fun _ => 0)) scale = 0 := by
  by_cases hj : j < rows.length
  · rw [List.getD_eq_getElem _ _ hj]
    exact h _ (List.getElem_mem hj)
  · rw [List.getD_eq_default _ _ (by omega)]
    simp [evaluate]

theorem evaluate_combine {n : ℕ} {rows : List (Row n)} {scale : Fin n → ℂ}
    (h : Satisfies rows scale) (weights : Weights) : evaluate (combine rows weights) scale = 0 := by
  induction weights with
  | nil => simp [combine,evaluate]
  | cons jc rest ih =>
    rcases jc with ⟨j,c⟩
    have he : evaluate (combine rows ((j,c)::rest)) scale =
        Algebraic.gaussianToComplex c * evaluate (rows.getD j (fun _ => 0)) scale +
          evaluate (combine rows rest) scale := by
      simp only [evaluate,combine,map_add,map_mul,add_mul,Finset.sum_add_distrib,Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [he,satisfies_getD h j,ih,mul_zero,add_zero]

def checkRow {n : ℕ} (rows : List (Row n)) (row : Row n) (weights : Weights) : Bool :=
  decide (row = combine rows weights)

theorem checked_row_sound {n : ℕ} {rows : List (Row n)} {row : Row n} {weights : Weights}
    (hc : checkRow rows row weights = true) {scale : Fin n → ℂ} (h : Satisfies rows scale) :
    evaluate row scale = 0 := by
  have he : row = combine rows weights := of_decide_eq_true hc
  rw [he]
  exact evaluate_combine h weights

structure Reduction (n : ℕ) where
  rows : List (Row n)
  witnesses : Fin rows.length → Weights

def Reduction.check {n : ℕ} (reduction : Reduction n) (rows : List (Row n)) : Bool :=
  decide (∀ i : Fin reduction.rows.length, checkRow rows (reduction.rows.get i) (reduction.witnesses i) = true)

theorem Reduction.sound {n : ℕ} (reduction : Reduction n) (rows : List (Row n))
    (hc : reduction.check rows = true) {scale : Fin n → ℂ} (h : Satisfies rows scale) :
    Satisfies reduction.rows scale := by
  have hall : ∀ i : Fin reduction.rows.length, checkRow rows (reduction.rows.get i) (reduction.witnesses i) = true :=
    of_decide_eq_true hc
  intro row hr
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hr
  exact checked_row_sound (hall i) h

inductive Certificate (n m d k t : ℕ) where
  | dead : Fin n → Weights → Certificate n m d k t
  | product : Fin t → (Fin m → Weights) → Certificate n m d k t
  | split : Fin d → (Fin k → Reduction n) → (Fin k → Certificate n m d k t) → Certificate n m d k t

namespace Certificate
variable {n m q d k t : ℕ}

def check (problem : Problem n m q d k t) (rows : List (Row n)) : Certificate n m d k t → Bool
  | .dead i weights => problem.live i && checkRow rows (unitRow i) weights
  | .product j weights => decide (problem.targets j (problem.targetPivot j) ≠ 0) &&
      decide (∀ i : Fin m, checkRow rows
        (wedgeRow problem.tensor (problem.targets j) (problem.targetPivot j) i) (weights i) = true)
  | .split c reductions children =>
      decide (∀ j : Fin k,
        (reductions j).check (rows++wedgeRows (problem.cards c) (problem.cardLines j) (problem.cardPivot j)) = true ∧
        check problem (reductions j).rows (children j) = true)

theorem sound (problem : Problem n m q d k t) (certificate : Certificate n m d k t) :
    ∀ rows, check problem rows certificate = true → ∀ scale : Fin n → ℂ,
      Satisfies rows scale → problem.Live scale → problem.SafeCards scale → problem.Accepted scale := by
  induction certificate with
  | dead i weights =>
    intro rows hc scale hrows hlive hsafe
    have hh := Bool.and_eq_true_iff.mp hc
    have hi := checked_row_sound hh.2 hrows
    rw [evaluate_unitRow] at hi
    exact False.elim (hlive i hh.1 hi)
  | product j weights =>
    intro rows hc scale hrows hlive hsafe
    have hh := Bool.and_eq_true_iff.mp hc
    have hp : problem.targets j (problem.targetPivot j) ≠ 0 := of_decide_eq_true hh.1
    have hall : ∀ i : Fin m, checkRow rows
        (wedgeRow problem.tensor (problem.targets j) (problem.targetPivot j) i) (weights i) = true :=
      of_decide_eq_true hh.2
    have hs : Satisfies (wedgeRows problem.tensor (problem.targets j) (problem.targetPivot j)) scale := by
      rw [satisfies_wedgeRows_iff]
      intro i
      exact checked_row_sound (hall i) hrows
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
    exact ih j _ (hall j).2 scale ((reductions j).sound _ (hall j).1 hadded) hlive hsafe

end Certificate

theorem solved_of_checked (state : DirectionTriple) (certificate : Certificate 4 64 60 48 960)
    (hc : certificate.check (problem state) (initialRows state) = true) : Solved state := by
  intro scale ha hs hn
  apply accepted_semantics state scale _ hn
  exact certificate.sound (problem state) (initialRows state) hc scale
    (admissible_initialRows state scale ha) (admissible_live state scale ha)
    (safeCards_semantics state scale ((allPhysicalSafe_iff_ordered _).mp hs))

end SparseCertificate
end
end Holant.Pauli.ExoticKlein.SixPort
