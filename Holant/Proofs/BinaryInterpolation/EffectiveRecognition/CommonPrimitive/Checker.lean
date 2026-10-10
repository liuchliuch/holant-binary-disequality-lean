import Holant.Proofs.BinaryInterpolation.EffectiveRecognition.CommonPrimitive.Primitive
import Holant.Proofs.BinaryInterpolation.EffectiveRecognition.CommonPrimitive.BoxLimit
import Holant.Proofs.AlgebraicRecognition.MatrixWitness


namespace Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.CommonPrimitive
open Holant.LocalDrafts.EffectiveAlgebraic
open PowerArithmetic CommonFieldCheck
open scoped BigOperators

theorem zero_iff {d : ℕ} (θ : ℂ) (c v : Vector d)
    (hmin : PowerArithmetic.polynomial c = minpoly ℚ θ) :
    CommonFieldCheck.zero v = true ↔ decode θ v = 0 := by
  rw [CommonFieldCheck.zero, decide_eq_true_eq]
  constructor
  · intro h
    rw [show v = 0 from funext h, map_zero]
  · intro h
    have hv : v = 0 := decode_injective θ c hmin (by simpa using h)
    intro i; exact congrFun hv i

theorem embedding_exact_zero {d : ℕ} (θ w : ℂ) (c : Vector d)
    (e : RationalPolynomialCode) (target : RootCode)
    (hmin : PowerArithmetic.polynomial c = minpoly ℚ θ)
    (he : Polynomial.aeval θ e.polynomial = w) (ht : target.Represents w) :
    zero (evalAt c (reduce c e) target.coefficients) = true := by
  have hr := relation_of_root θ c (by rw [hmin]; exact minpoly.aeval ℚ θ)
  apply (zero_iff θ c _ hmin).mpr
  rw [decode_evalAt θ c hr, decode_reduce θ c hr, he]
  exact ht.2.2.1

theorem family_check_small {d m : ℕ} (θ : ℂ) (c : Vector d)
    (e : Fin m → RationalPolynomialCode) (target : Fin m → RootCode) (w : Fin m → ℂ)
    (hmin : PowerArithmetic.polynomial c = minpoly ℚ θ)
    (he : ∀ i, Polynomial.aeval θ (e i).polynomial = w i)
    (ht : ∀ i, (target i).Represents (w i)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ b : RationalBox, BoxLimit.Small θ ε b →
      checkFamily c b e target = true := by
  obtain ⟨ε, hε, hb⟩ := BoxLimit.family_small θ e (fun i => (target i).rectangle)
    (fun i => by rw [he]; exact (ht i).2.1)
  refine ⟨ε, hε, ?_⟩
  intro b hs
  simp only [checkFamily, decide_eq_true_eq]
  intro i
  simp only [checkEmbedding,Bool.and_eq_true_eq_eq_true_and_eq_true]
  exact ⟨embedding_exact_zero θ (w i) c (e i) (target i) hmin (he i) (ht i),
    hb b hs i⟩

/-- The existing EncodedSystem decode helpers are private. This public bridge
proves the exact evaluator equation needed for the converse; no evaluator is
reimplemented and no successful-system-check premise is introduced. -/
theorem materialize_value {d m n : ℕ} (θ : ℂ) (c : Vector d)
    (hr : θ ^ (d + 1) = decode θ c) (a : Fin m → Vector d)
    (x : Fin n → Vector d) (e : EncodedSystem.Equation m n) :
    decode θ (FixedSystem.evalEquation (data c) x (EncodedSystem.materialize a e)) =
      MvPolynomial.aeval (fun i => decode θ (x i))
        (EncodedSystem.polynomial (fun i => decode θ (a i)) e) := by
  have hprod (n : ℕ) (v : Fin n → Vector d) :
      decode θ (FixedSystem.productCode (data c) n v) = ∏ i, decode θ (v i) := by
    induction n with
    | zero => simp [FixedSystem.productCode, data]
    | succ n ih =>
      rw [FixedSystem.productCode, decode_mul θ c _ _ hr, ih, Fin.prod_univ_succ]
      rfl
  have hterm (t : EncodedSystem.Term m n) :
      decode θ (FixedSystem.evalTerm (data c) x (a t.1, t.2)) =
        decode θ (a t.1) * ∏ i, (decode θ (x i)) ^ t.2 i := by
    rw [FixedSystem.evalTerm, decode_mul θ c _ _ hr, hprod]
    simp only [decode_powerCode θ c hr]
  induction e with
  | nil => simp [EncodedSystem.materialize, FixedSystem.evalEquation, EncodedSystem.polynomial]
  | cons t ts ih =>
    change decode θ (FixedSystem.evalTerm (data c) x (a t.1,t.2) +
      FixedSystem.evalEquation (data c) x (EncodedSystem.materialize a ts)) = _
    rw [map_add,hterm,ih]
    simp [EncodedSystem.polynomial]

theorem system_exact {d m n : ℕ} (θ : ℂ) (c : Vector d)
    (e : Fin m → RationalPolynomialCode) (w : Fin m → ℂ) (y : Fin n → ℂ)
    (x : Fin n → Vector d) (S : EncodedSystem.System m n)
    (hmin : PowerArithmetic.polynomial c = minpoly ℚ θ)
    (he : ∀ i, Polynomial.aeval θ (e i).polynomial = w i)
    (hx : ∀ j, decode θ (x j) = y j)
    (hy : ∀ f ∈ S, MvPolynomial.aeval y (EncodedSystem.polynomial w f) = 0) :
    FixedSystem.checkSystem (data c) (S.map (EncodedSystem.materialize (familyCoordinates c e))) x = true := by
  have hr := relation_of_root θ c (by rw [hmin]; exact minpoly.aeval ℚ θ)
  have hc : (fun i => decode θ (familyCoordinates c e i)) = w := by
    funext i; rw [familyCoordinates, decode_reduce θ c hr, he]
  simp only [FixedSystem.checkSystem, List.all_eq_true, decide_eq_true_eq]
  intro f hf
  obtain ⟨f, hmem, rfl⟩ := List.mem_map.mp hf
  have hz : decode θ (FixedSystem.evalEquation (data c) x
      (EncodedSystem.materialize (familyCoordinates c e) f)) = 0 := by
    rw [materialize_value θ c hr, hc, funext hx]
    exact hy f hmem
  have hv := (zero_iff θ c _ hmin).mpr hz
  simpa only [zero, decide_eq_true_eq] using hv

/-- The system precheck succeeds for every sufficiently small primitive box.
The true source equations, not the check result, are the mathematical premise. -/
theorem system_check_small {d m n : ℕ} (θ : ℂ) (c : Vector d)
    (e : Fin m → RationalPolynomialCode) (target : Fin m → RootCode)
    (w : Fin m → ℂ) (y : Fin n → ℂ) (x : Fin n → Vector d)
    (S : EncodedSystem.System m n)
    (hmin : PowerArithmetic.polynomial c = minpoly ℚ θ)
    (he : ∀ i, Polynomial.aeval θ (e i).polynomial = w i)
    (ht : ∀ i, (target i).Represents (w i)) (hx : ∀ j, decode θ (x j) = y j)
    (hy : ∀ f ∈ S, MvPolynomial.aeval y (EncodedSystem.polynomial w f) = 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ b : RationalBox, BoxLimit.Small θ ε b →
      EncodedSystem.check c b e target S x = true := by
  obtain ⟨ε, hε, hb⟩ := family_check_small θ c e target w hmin he ht
  refine ⟨ε, hε, fun b hs => ?_⟩
  simp only [EncodedSystem.check,Bool.and_eq_true_eq_eq_true_and_eq_true]
  exact ⟨hb b hs, system_exact θ c e w y x S hmin he hx hy⟩

/-- The existing matrix guard uses positions 0,1,2,3,4 of the same tuple. -/
theorem guard_exact {d k : ℕ} (θ : ℂ) (c : Vector d) (x : MatrixWitness.Candidate d k)
    (y : Fin (5 + k) → ℂ) (hmin : PowerArithmetic.polynomial c = minpoly ℚ θ)
    (hx : ∀ j, decode θ (x j) = y j)
    (hy : y (Fin.castAdd k 4) *
      (y (Fin.castAdd k 0) * y (Fin.castAdd k 3) -
        y (Fin.castAdd k 1) * y (Fin.castAdd k 2)) = 1) :
    MatrixWitness.checkGuard c x = true := by
  have hr := relation_of_root θ c (by rw [hmin]; exact minpoly.aeval ℚ θ)
  apply (zero_iff θ c _ hmin).mpr
  change decode θ ((data c).mulCode (x (Fin.castAdd k 4))
    (MatrixWitness.determinantCode c x) - (data c).unitCode) = 0
  simp only [MatrixWitness.determinantCode,map_sub,decode_mul θ c _ _ hr]
  simpa [data,hx,MatrixWitness.matrixCode,MatrixWitness.index] using sub_eq_zero.mpr hy

end Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.CommonPrimitive
