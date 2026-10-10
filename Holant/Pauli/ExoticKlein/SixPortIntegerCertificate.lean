import Holant.Pauli.ExoticKlein.SixPortIntegerArithmetic

/-! Denominator-cleared scale certificates. The finite computation uses only
Gaussian integers; soundness still quantifies over arbitrary complex scales. -/
namespace Holant.Pauli.ExoticKlein.SixPort
noncomputable section
open LinearCertificate
open scoped BigOperators
namespace IntegerCertificate

abbrev IRow (n : ℕ) := Fin n → GZ
abbrev Weights := List (ℕ × GZ)
def mapRow {n : ℕ} (row : IRow n) : Row n := fun i => integerToGaussian (row i)
def mapRows {n : ℕ} (rows : List (IRow n)) : List (Row n) := rows.map mapRow

def combine {n : ℕ} (rows : List (IRow n)) : Weights → IRow n
  | [] => fun _ => 0
  | (j,c)::rest => fun i => c*(rows.getD j (fun _ => 0)) i + combine rows rest i

theorem mapRow_getD {n : ℕ} (rows : List (IRow n)) (j : ℕ) :
    mapRow (rows.getD j (fun _ => 0)) = (mapRows rows).getD j (fun _ => 0) := by
  have hz : mapRow (fun _ : Fin n => (0 : GZ)) = (fun _ => (0 : Q)) := by
    funext i
    exact map_zero _
  simpa only [mapRows,hz] using
    (List.getD_map (l := rows) (d := fun _ => (0 : GZ)) (n := j) mapRow).symm

theorem map_combine {n : ℕ} (rows : List (IRow n)) (weights : Weights) :
    mapRow (combine rows weights) = SparseCertificate.combine (mapRows rows)
      (weights.map (fun jc => (jc.1,integerToGaussian jc.2))) := by
  induction weights with
  | nil => funext i; exact map_zero _
  | cons jc rest ih =>
    rcases jc with ⟨j,c⟩
    funext i
    simp only [combine,mapRow,map_add,map_mul,List.map_cons,SparseCertificate.combine]
    rw [←mapRow_getD]
    exact congrArg (fun z => integerToGaussian c*integerToGaussian ((rows.getD j (fun _ => 0)) i)+z)
      (congrFun ih i)

structure Witness where
  denominator : ℕ
  weights : Weights

def checkRow {n : ℕ} (rows : List (IRow n)) (row : IRow n) (w : Witness) : Bool :=
  decide (0 < w.denominator) && decide ((fun i => (w.denominator : GZ)*row i) = combine rows w.weights)

theorem checked_row_sound {n : ℕ} {rows : List (IRow n)} {row : IRow n} {w : Witness}
    (hc : checkRow rows row w = true) {scale : Fin n → ℂ} (hs : Satisfies (mapRows rows) scale) :
    evaluate (mapRow row) scale = 0 := by
  have hcheck := Bool.and_eq_true_iff.mp hc
  have hd : 0 < w.denominator := of_decide_eq_true hcheck.1
  have he : (fun i => (w.denominator : GZ)*row i) = combine rows w.weights := of_decide_eq_true hcheck.2
  have hz : evaluate (mapRow (combine rows w.weights)) scale = 0 := by
    rw [map_combine]
    exact SparseCertificate.evaluate_combine hs _
  rw [←he] at hz
  have hh : evaluate (mapRow (fun i => (w.denominator : GZ)*row i)) scale =
      (w.denominator : ℂ)*evaluate (mapRow row) scale := by
    simp only [evaluate,mapRow,map_mul,map_natCast,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hh] at hz
  exact (mul_eq_zero.mp hz).resolve_left (by exact_mod_cast (ne_of_gt hd))

def unitRow {n : ℕ} (i : Fin n) : IRow n := fun j => if j = i then 1 else 0
@[simp] theorem map_unitRow {n : ℕ} (i : Fin n) : mapRow (unitRow i) = LinearCertificate.unitRow i := by
  funext j
  simp [mapRow,unitRow,LinearCertificate.unitRow]

def wedgeRow {n m : ℕ} (matrix : Fin m → IRow n) (target : Fin m → GZ) (pivot i : Fin m) : IRow n :=
  fun j => target pivot*matrix i j-target i*matrix pivot j

def wedgeRows {n m : ℕ} (matrix : Fin m → IRow n) (target : Fin m → GZ) (pivot : Fin m) : List (IRow n) :=
  List.ofFn (wedgeRow matrix target pivot)

theorem map_wedgeRow {n m : ℕ} (matrix : Fin m → IRow n) (target : Fin m → GZ) (pivot i : Fin m) :
    mapRow (wedgeRow matrix target pivot i) = LinearCertificate.wedgeRow
      (fun i => mapRow (matrix i)) (fun i => integerToGaussian (target i)) pivot i := by
  funext j
  simp [mapRow,wedgeRow,LinearCertificate.wedgeRow]

theorem map_wedgeRows {n m : ℕ} (matrix : Fin m → IRow n) (target : Fin m → GZ) (pivot : Fin m) :
    mapRows (wedgeRows matrix target pivot) = LinearCertificate.wedgeRows
      (fun i => mapRow (matrix i)) (fun i => integerToGaussian (target i)) pivot := by
  simp only [mapRows,wedgeRows,LinearCertificate.wedgeRows,List.map_ofFn]
  congr 1
  funext i
  exact map_wedgeRow _ _ _ _

structure Reduction (n : ℕ) where
  rows : List (IRow n)
  witnesses : Fin rows.length → Witness

def Reduction.check {n : ℕ} (reduction : Reduction n) (rows : List (IRow n)) : Bool :=
  decide (∀ i : Fin reduction.rows.length, checkRow rows (reduction.rows.get i) (reduction.witnesses i) = true)

theorem Reduction.sound {n : ℕ} (reduction : Reduction n) (rows : List (IRow n))
    (hc : reduction.check rows = true) {scale : Fin n → ℂ} (h : Satisfies (mapRows rows) scale) :
    Satisfies (mapRows reduction.rows) scale := by
  have hall : ∀ i : Fin reduction.rows.length, checkRow rows (reduction.rows.get i) (reduction.witnesses i) = true :=
    of_decide_eq_true hc
  intro row hr
  obtain ⟨r,hrmem,rfl⟩ := List.mem_map.mp hr
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hrmem
  exact checked_row_sound (hall i) h

structure Problem (n m q d k t : ℕ) where
  tensor : Fin m → IRow n
  cards : Fin d → Fin q → IRow n
  cardLines : Fin k → Fin q → GZ
  cardPivot : Fin k → Fin q
  targets : Fin t → Fin m → GZ
  targetPivot : Fin t → Fin m
  live : Fin n → Bool

def Problem.toProblem {n m q d k t : ℕ} (p : Problem n m q d k t) : LinearCertificate.Problem n m q d k t where
  tensor i := mapRow (p.tensor i)
  cards c i := mapRow (p.cards c i)
  cardLines j i := integerToGaussian (p.cardLines j i)
  cardPivot := p.cardPivot
  targets j i := integerToGaussian (p.targets j i)
  targetPivot := p.targetPivot
  live := p.live

inductive Certificate (n m d k t : ℕ) where
  | dead : Fin n → Witness → Certificate n m d k t
  | product : Fin t → (Fin m → Witness) → Certificate n m d k t
  | split : Fin d → (Fin k → Reduction n) → (Fin k → Certificate n m d k t) → Certificate n m d k t

namespace Certificate
variable {n m q d k t : ℕ}

def check (problem : Problem n m q d k t) (rows : List (IRow n)) : Certificate n m d k t → Bool
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
      Satisfies (mapRows rows) scale → problem.toProblem.Live scale →
      problem.toProblem.SafeCards scale → problem.toProblem.Accepted scale := by
  induction certificate with
  | dead i weights =>
    intro rows hc scale hrows hlive hsafe
    have hh := Bool.and_eq_true_iff.mp hc
    have hi := checked_row_sound hh.2 hrows
    rw [map_unitRow,evaluate_unitRow] at hi
    exact False.elim (hlive i hh.1 hi)
  | product j weights =>
    intro rows hc scale hrows hlive hsafe
    have hh := Bool.and_eq_true_iff.mp hc
    have hp : problem.targets j (problem.targetPivot j) ≠ 0 := of_decide_eq_true hh.1
    have hp' : integerToGaussian (problem.targets j (problem.targetPivot j)) ≠ 0 := by
      intro h
      exact hp (integerToGaussian_injective (h.trans (map_zero _).symm))
    have hall : ∀ i : Fin m, checkRow rows
        (wedgeRow problem.tensor (problem.targets j) (problem.targetPivot j) i) (weights i) = true :=
      of_decide_eq_true hh.2
    have hs : Satisfies (LinearCertificate.wedgeRows problem.toProblem.tensor
        (problem.toProblem.targets j) (problem.targetPivot j)) scale := by
      rw [satisfies_wedgeRows_iff]
      intro i
      have hi := checked_row_sound (hall i) hrows
      rw [map_wedgeRow] at hi
      exact hi
    obtain ⟨s,he⟩ := wedgeRows_implies_line problem.toProblem.tensor
      (problem.toProblem.targets j) (problem.targetPivot j) hp' scale hs
    exact ⟨j,s,he⟩
  | split c reductions children ih =>
    intro rows hc scale hrows hlive hsafe
    have hall : ∀ j : Fin k,
        (reductions j).check (rows++wedgeRows (problem.cards c) (problem.cardLines j) (problem.cardPivot j)) = true ∧
        check problem (reductions j).rows (children j) = true := of_decide_eq_true hc
    obtain ⟨j,s,he⟩ := hsafe c
    have hadded : Satisfies (mapRows (rows++wedgeRows (problem.cards c) (problem.cardLines j) (problem.cardPivot j))) scale := by
      rw [mapRows,List.map_append]
      change Satisfies (mapRows rows ++ mapRows (wedgeRows _ _ _)) scale
      rw [map_wedgeRows]
      exact (satisfies_append _ _ _).mpr ⟨hrows,line_implies_wedgeRows _ _ _ _ s he⟩
    exact ih j _ (hall j).2 scale ((reductions j).sound _ (hall j).1 hadded) hlive hsafe

end Certificate
end IntegerCertificate
end
end Holant.Pauli.ExoticKlein.SixPort
