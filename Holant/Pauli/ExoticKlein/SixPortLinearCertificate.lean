import Holant.Pauli.ExoticKlein.GaussianScalars
import Mathlib.Data.List.GetD

/-! Exact row-combination certificates for the six-port scale problem.
The checker works over Q(i); its soundness quantifies over arbitrary complex
scales. Line preimages include the zero output and never divide by a scale. -/
namespace Holant.Pauli.ExoticKlein.SixPort.LinearCertificate
noncomputable section
open scoped BigOperators
abbrev Q := Algebraic.GaussianRational
abbrev Row (n : ℕ) := Fin n → Q

 def evaluate {n : ℕ} (row : Row n) (scale : Fin n → ℂ) : ℂ :=
  ∑ i, Algebraic.gaussianToComplex (row i)*scale i

 def output {n m : ℕ} (matrix : Fin m → Row n) (scale : Fin n → ℂ) : Fin m → ℂ :=
  fun i => evaluate (matrix i) scale

 def Satisfies {n : ℕ} (rows : List (Row n)) (scale : Fin n → ℂ) : Prop :=
  ∀ row ∈ rows, evaluate row scale = 0

/-- A certificate row is an explicit exact linear combination of supplied rows. -/
 def combine {n : ℕ} (rows : List (Row n)) (weights : List Q) : Row n :=
  fun i => ∑ j : Fin rows.length, weights.getD j.val 0 * rows.get j i

 theorem evaluate_combine {n : ℕ} (rows : List (Row n)) (weights : List Q) (scale : Fin n → ℂ) :
    evaluate (combine rows weights) scale =
      ∑ j : Fin rows.length, Algebraic.gaussianToComplex (weights.getD j.val 0)*evaluate (rows.get j) scale := by
  simp only [evaluate,combine,map_sum,map_mul,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro i hi
  ring

 theorem Satisfies.combine {n : ℕ} {rows : List (Row n)} {scale : Fin n → ℂ}
    (h : Satisfies rows scale) (weights : List Q) : evaluate (combine rows weights) scale = 0 := by
  rw [evaluate_combine]
  apply Finset.sum_eq_zero
  intro j hj
  rw [h (rows.get j) (List.get_mem _ _),mul_zero]

 def unitRow {n : ℕ} (i : Fin n) : Row n := fun j => if j = i then 1 else 0

@[simp] theorem evaluate_unitRow {n : ℕ} (i : Fin n) (scale : Fin n → ℂ) :
    evaluate (unitRow i) scale = scale i := by simp [evaluate,unitRow]

 def CheckRow {n : ℕ} (rows : List (Row n)) (row : Row n) (weights : List Q) : Bool :=
  decide (row = combine rows weights)

 theorem checked_row_sound {n : ℕ} (rows : List (Row n)) (row : Row n) (weights : List Q)
    (hcheck : CheckRow rows row weights = true) {scale : Fin n → ℂ} (h : Satisfies rows scale) :
    evaluate row scale = 0 := by
  have he : row = combine rows weights := of_decide_eq_true hcheck
  rw [he]
  exact h.combine weights

 structure Reduction (n : ℕ) where
  rows : List (Row n)
  witnesses : Fin rows.length → List Q

 def Reduction.check {n : ℕ} (reduction : Reduction n) (rows : List (Row n)) : Bool :=
  decide (∀ i : Fin reduction.rows.length, CheckRow rows (reduction.rows.get i) (reduction.witnesses i) = true)

 theorem Reduction.sound {n : ℕ} (reduction : Reduction n) (rows : List (Row n))
    (hc : reduction.check rows = true) {scale : Fin n → ℂ} (h : Satisfies rows scale) :
    Satisfies reduction.rows scale := by
  have hall : ∀ i : Fin reduction.rows.length, CheckRow rows (reduction.rows.get i) (reduction.witnesses i) = true :=
    of_decide_eq_true hc
  intro row hr
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hr
  exact checked_row_sound rows _ _ (hall i) h

 theorem satisfies_append {n : ℕ} (left right : List (Row n)) (scale : Fin n → ℂ) :
    Satisfies (left++right) scale ↔ Satisfies left scale ∧ Satisfies right scale := by
  simp only [Satisfies,List.mem_append,or_imp,forall_and]

/-- All target-line equations use one fixed nonzero target pivot. They are
homogeneous in the input scales, so every cancellation locus is retained. -/
 def wedgeRow {n m : ℕ} (matrix : Fin m → Row n) (target : Fin m → Q) (pivot i : Fin m) : Row n :=
  fun j => target pivot*matrix i j-target i*matrix pivot j

 def wedgeRows {n m : ℕ} (matrix : Fin m → Row n) (target : Fin m → Q) (pivot : Fin m) : List (Row n) :=
  List.ofFn (wedgeRow matrix target pivot)

 theorem evaluate_wedgeRow {n m : ℕ} (matrix : Fin m → Row n) (target : Fin m → Q)
    (pivot i : Fin m) (scale : Fin n → ℂ) :
    evaluate (wedgeRow matrix target pivot i) scale =
      Algebraic.gaussianToComplex (target pivot)*output matrix scale i-
      Algebraic.gaussianToComplex (target i)*output matrix scale pivot := by
  simp only [evaluate,wedgeRow,output,map_sub,map_mul,sub_mul,Finset.sum_sub_distrib,Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro j hj <;> ring

 theorem satisfies_wedgeRows_iff {n m : ℕ} (matrix : Fin m → Row n) (target : Fin m → Q)
    (pivot : Fin m) (scale : Fin n → ℂ) :
    Satisfies (wedgeRows matrix target pivot) scale ↔ ∀ i, evaluate (wedgeRow matrix target pivot i) scale = 0 := by
  simp only [Satisfies,wedgeRows,List.mem_ofFn]
  constructor
  · intro h i
    exact h _ ⟨i,rfl⟩
  · intro h row hr
    obtain ⟨i,rfl⟩ := hr
    exact h i

 theorem line_implies_wedgeRows {n m : ℕ} (matrix : Fin m → Row n) (target : Fin m → Q)
    (pivot : Fin m) (scale : Fin n → ℂ) (s : ℂ)
    (h : ∀ i, output matrix scale i = s*Algebraic.gaussianToComplex (target i)) :
    Satisfies (wedgeRows matrix target pivot) scale := by
  rw [satisfies_wedgeRows_iff]
  intro i
  rw [evaluate_wedgeRow,h i,h pivot]
  ring

/-- Conversely, a checked line preimage describes exactly all scalar
multiples of the target, with scalar zero explicitly allowed. -/
 theorem wedgeRows_implies_line {n m : ℕ} (matrix : Fin m → Row n) (target : Fin m → Q)
    (pivot : Fin m) (hp : target pivot ≠ 0) (scale : Fin n → ℂ)
    (h : Satisfies (wedgeRows matrix target pivot) scale) :
    ∃ s : ℂ, ∀ i, output matrix scale i = s*Algebraic.gaussianToComplex (target i) := by
  have hp' : Algebraic.gaussianToComplex (target pivot) ≠ 0 :=
    (map_ne_zero Algebraic.gaussianToComplex).mpr hp
  refine ⟨output matrix scale pivot / Algebraic.gaussianToComplex (target pivot),?_⟩
  intro i
  have hi := (satisfies_wedgeRows_iff matrix target pivot scale).mp h i
  rw [evaluate_wedgeRow,sub_eq_zero] at hi
  calc
    output matrix scale i =
        (Algebraic.gaussianToComplex (target i)*output matrix scale pivot) /
          Algebraic.gaussianToComplex (target pivot) :=
      (eq_div_iff hp').mpr (by simpa only [mul_comm] using hi)
    _ = _ := by ring


end
end Holant.Pauli.ExoticKlein.SixPort.LinearCertificate
