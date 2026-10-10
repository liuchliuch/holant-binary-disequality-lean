import Holant.Proofs.AlgebraicRecognition.FixedSystem
import Mathlib.RingTheory.PowerBasis
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic


namespace Holant.LocalDrafts.EffectiveAlgebraic.PowerArithmetic
open Holant.Algebraic
open scoped BigOperators

abbrev Vector (d : ℕ) := Fin (d + 1) → ℚ

def unit (d : ℕ) : Vector d := Pi.single 0 1

/-- Reduction of X times a basis monomial. -/
def stepVector {d : ℕ} (c : Vector d) (i : Fin (d + 1)) : Vector d :=
  if h : i.val + 1 < d + 1 then Pi.single ⟨i.val + 1, h⟩ 1 else c

def shift {d : ℕ} (c v : Vector d) : Vector d :=
  ∑ i, v i • stepVector c i

def power {d : ℕ} (c : Vector d) : ℕ → Vector d
  | 0 => unit d
  | k + 1 => shift c (power c k)

/-- Actual rational multiplication data for all basis pairs. -/
def data {d : ℕ} (c : Vector d) : ArithmeticData (d + 1) where
  unitCode := unit d
  mulTable i j := power c (i.val + j.val)

noncomputable def polynomial {d : ℕ} (c : Vector d) : Polynomial ℚ :=
  Polynomial.X ^ (d + 1) -
    ∑ i : Fin (d + 1), Polynomial.C (c i) * Polynomial.X ^ i.val

theorem polynomial_natDegree {d : ℕ} (c : Vector d) :
    (polynomial c).natDegree = d + 1 := by
  apply Polynomial.natDegree_eq_of_degree_eq_some
  have hlt :
      (∑ i : Fin (d + 1), Polynomial.C (c i) * Polynomial.X ^ i.val).degree <
        ((Polynomial.X : Polynomial ℚ) ^ (d + 1)).degree := by
    simpa only [Polynomial.degree_X_pow] using Polynomial.degree_sum_fin_lt c
  rw [polynomial, Polynomial.degree_sub_eq_left_of_degree_lt hlt,
    Polynomial.degree_X_pow]

section Semantics
variable {K : Type*} [Field K] [Algebra ℚ K] {d : ℕ}

noncomputable def decode (z : K) : Vector d →ₗ[ℚ] K :=
  Fintype.linearCombination ℚ (fun i : Fin (d + 1) => z ^ i.val)

theorem decode_apply (z : K) (v : Vector d) :
    decode z v = ∑ i, v i • z ^ i.val := rfl

@[simp] theorem decode_single (z : K) (i : Fin (d + 1)) (q : ℚ) :
    decode z (Pi.single i q) = q • z ^ i.val :=
  Fintype.linearCombination_apply_single _ _ _ _

@[simp] theorem decode_unit (z : K) : decode z (unit d) = 1 := by
  simp [unit]

theorem relation_of_root (z : K) (c : Vector d)
    (h : Polynomial.aeval z (polynomial c) = 0) :
    z ^ (d + 1) = decode z c := by
  apply sub_eq_zero.mp
  simpa [polynomial, decode_apply, Algebra.smul_def] using h

theorem decode_stepVector (z : K) (c : Vector d)
    (hz : z ^ (d + 1) = decode z c) (i : Fin (d + 1)) :
    decode z (stepVector c i) = z ^ i.val * z := by
  unfold stepVector
  split_ifs with hi
  · simp [pow_succ]
  · have hi' : i.val + 1 = d + 1 := by omega
    rw [← hz, ← pow_succ, hi']

theorem decode_shift (z : K) (c v : Vector d)
    (hz : z ^ (d + 1) = decode z c) :
    decode z (shift c v) = decode z v * z := by
  simp only [shift, map_sum, map_smul, decode_stepVector z c hz,
    decode_apply, Finset.sum_mul, smul_mul_assoc]

theorem decode_power (z : K) (c : Vector d)
    (hz : z ^ (d + 1) = decode z c) (k : ℕ) :
    decode z (power c k) = z ^ k := by
  induction k with
  | zero => simp [power]
  | succ k ih => rw [power, decode_shift z c _ hz, ih, pow_succ]

/-- Multiplication correctness is derived from the monic root relation. -/
theorem decode_mul (z : K) (c u v : Vector d)
    (hz : z ^ (d + 1) = decode z c) :
    decode z ((data c).mulCode u v) = decode z u * decode z v := by
  simp only [ArithmeticData.mulCode, data, map_sum, map_smul, decode_power z c hz,
    pow_add, decode_apply, Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm]
  exact Finset.sum_comm

theorem decode_injective (z : K) (c : Vector d)
    (hmin : polynomial c = minpoly ℚ z) : Function.Injective (decode (d := d) z) := by
  have hdeg : (minpoly ℚ z).natDegree = d + 1 := by
    rw [← hmin, polynomial_natDegree]
  have hi : LinearIndependent ℚ (fun i : Fin (d + 1) => z ^ i.val) := by
    simpa only [Function.comp_def, Fin.val_cast] using
      (linearIndependent_pow (K := ℚ) z).comp
        (Fin.cast hdeg.symm) (Fin.cast_injective hdeg.symm)
  exact hi.fintypeLinearCombination_injective

end Semantics

/-- Exact equality is finite rational-coordinate equality. -/
def equal {d : ℕ} (u v : Vector d) : Bool := decide (∀ i, u i = v i)

theorem equal_iff {K : Type*} [Field K] [Algebra ℚ K] {d : ℕ}
    (z : K) (c u v : Vector d) (hmin : polynomial c = minpoly ℚ z) :
    equal u v = true ↔ decode z u = decode z v := by
  simp only [equal, decide_eq_true_eq]
  exact (funext_iff.symm).trans (decode_injective z c hmin).eq_iff.symm

@[simp] theorem decode_add {K : Type*} [Field K] [Algebra ℚ K] {d : ℕ}
    (z : K) (u v : Vector d) : decode z (u + v) = decode z u + decode z v :=
  (decode z).map_add u v

@[simp] theorem decode_neg {K : Type*} [Field K] [Algebra ℚ K] {d : ℕ}
    (z : K) (u : Vector d) : decode z (-u) = -decode z u :=
  (decode z).map_neg u

theorem reindexedBasis_decode {K : Type*} [Field K] [Algebra ℚ K]
    (b : PowerBasis ℚ K) {d : ℕ} (hdim : b.dim = d + 1) (c : Vector d)
    : (b.basis.reindex (finCongr hdim)).equivFun.symm c = decode b.gen c := by
  rw [Module.Basis.equivFun_symm_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp [Module.Basis.reindex_apply, PowerBasis.basis_eq_pow]

/-- Derive a genuine existing FixedField presentation from a power basis and
its root equation. Only `data c` is used by runtime algorithms. -/
noncomputable def presentation {K : Type*} [Field K] [Algebra ℚ K]
    (b : PowerBasis ℚ K) {d : ℕ} (hdim : b.dim = d + 1) (c : Vector d)
    (hc : b.gen ^ (d + 1) = decode b.gen c) : FixedField K (d + 1) where
  toArithmeticData := data c
  basis := b.basis.reindex (finCongr hdim)
  unit_spec := by
    rw [reindexedBasis_decode]
    exact decode_unit b.gen
  mul_spec i j := by
    rw [reindexedBasis_decode]
    simp only [data, decode_power b.gen c hc, pow_add]
    simp [Module.Basis.reindex_apply, PowerBasis.basis_eq_pow]

open scoped IntermediateField in
/-- A single algebraic root with its minimal polynomial gives a concrete field
presentation. Its rational table is computed from c; the semantic field/basis
serves only to certify the table. No arithmetic correctness premise is supplied. -/
noncomputable def rootPresentation {K : Type*} [Field K] [Algebra ℚ K]
    (z : K) (hz : IsIntegral ℚ z) {d : ℕ} (c : Vector d)
    (hmin : polynomial c = minpoly ℚ z) : FixedField ℚ⟮z⟯ (d + 1) := by
  let b := IntermediateField.adjoin.powerBasis hz
  have hdim : b.dim = d + 1 := by
    change (minpoly ℚ z).natDegree = d + 1
    rw [← hmin, polynomial_natDegree]
  apply presentation b hdim c
  apply Subtype.val_injective
  have hr : z ^ (d + 1) = decode z c :=
    relation_of_root z c (by rw [hmin]; exact minpoly.aeval ℚ z)
  simpa [b, decode_apply, Algebra.smul_def, IntermediateField.adjoin.powerBasis_gen] using hr

open scoped IntermediateField in
@[simp] theorem rootPresentation_data {K : Type*} [Field K] [Algebra ℚ K]
    (z : K) (hz : IsIntegral ℚ z) {d : ℕ} (c : Vector d)
    (hmin : polynomial c = minpoly ℚ z) :
    (rootPresentation z hz c hmin).toArithmeticData = data c := rfl

end Holant.LocalDrafts.EffectiveAlgebraic.PowerArithmetic
