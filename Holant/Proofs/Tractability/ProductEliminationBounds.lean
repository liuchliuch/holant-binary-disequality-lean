import Holant.Proofs.Tractability.ProductElimination


namespace Holant.LocalDrafts.Tractability.ProductElimination

variable {K : Type*} [CommSemiring K]

theorem tailFactors_length_le {n : ℕ} (fs : List (Factor K (n + 1))) :
    (tailFactors fs).length ≤ fs.length := by
  induction fs with
  | nil => simp [tailFactors]
  | cons f fs ih =>
    cases h : f.splitHead.2 <;>
      simp [tailFactors, List.filterMap_cons, h] at * <;> omega

/-- The same elimination, annotated by field additions and multiplications.
Substituting signed variable addresses performs no field arithmetic. -/
def run : {n : ℕ} → List (Factor K n) → K × ℕ
  | 0, fs => (weight fs Fin.elim0, fs.length)
  | n + 1, fs => match pivot fs with
    | some (j, p) => run (fs.map (Factor.substitute (redirect j p)))
    | none =>
      let rest := run (tailFactors fs)
      ((headWeight fs false + headWeight fs true) * rest.1,
        2 * fs.length + 2 + rest.2)

theorem run_value {n : ℕ} (fs : List (Factor K n)) : (run fs).1 = evaluate fs := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases hp : pivot fs with
    | none => simp only [run, evaluate, hp, ih]
    | some jp => rcases jp with ⟨j, p⟩; simp only [run, evaluate, hp, ih]

theorem run_exact {n : ℕ} (fs : List (Factor K n)) : (run fs).1 = partition fs := by
  rw [run_value, evaluate_eq_partition]

/-- Factor count never increases, so repeated substitution cannot cause a
formula-size explosion. The quadratic bound includes isolated/free variables. -/
theorem run_operations_le {n : ℕ} (fs : List (Factor K n)) :
    (run fs).2 ≤ (2 * n + 1) * fs.length + 2 * n := by
  induction n with
  | zero => simp [run]
  | succ n ih =>
    cases hp : pivot fs with
    | none =>
      have hr := ih (tailFactors fs)
      have hl := Nat.mul_le_mul_left (2 * n + 1) (tailFactors_length_le fs)
      simp only [run, hp]
      nlinarith
    | some jp =>
      rcases jp with ⟨j, p⟩
      have hr := ih (fs.map (Factor.substitute (redirect j p)))
      simp only [List.length_map] at hr
      simp only [run, hp]
      nlinarith

/-- Count factor visits for one pivot scan and one rewrite pass per stage;
this deliberately separates syntactic work from encoded machine execution. -/
def factorVisits : {n : ℕ} → List (Factor K n) → ℕ
  | 0, fs => fs.length
  | n + 1, fs => 2 * fs.length + match pivot fs with
    | some (j, p) => factorVisits (fs.map (Factor.substitute (redirect j p)))
    | none => factorVisits (tailFactors fs)

theorem factorVisits_le {n : ℕ} (fs : List (Factor K n)) :
    factorVisits fs ≤ (2 * n + 1) * fs.length := by
  induction n with
  | zero => simp [factorVisits]
  | succ n ih =>
    cases hp : pivot fs with
    | none =>
      have hr := ih (tailFactors fs)
      have hl := Nat.mul_le_mul_left (2 * n + 1) (tailFactors_length_le fs)
      simp only [factorVisits, hp]
      nlinarith
    | some jp =>
      rcases jp with ⟨j, p⟩
      have hr := ih (fs.map (Factor.substitute (redirect j p)))
      simp only [List.length_map] at hr
      simp only [factorVisits, hp]
      nlinarith

end Holant.LocalDrafts.Tractability.ProductElimination
