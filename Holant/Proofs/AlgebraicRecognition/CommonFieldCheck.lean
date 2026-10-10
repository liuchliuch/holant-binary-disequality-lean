import Holant.Proofs.AlgebraicRecognition.IntervalArithmetic
import Holant.Proofs.AlgebraicRecognition.PowerArithmetic


namespace Holant.LocalDrafts.EffectiveAlgebraic.CommonFieldCheck
open PowerArithmetic

def reduce {d : ℕ} (c : Vector d) : RationalPolynomialCode → Vector d
  | [] => 0
  | (k, q) :: rest => q • power c k + reduce c rest

def evalAt {d : ℕ} (c v : Vector d) : RationalPolynomialCode → Vector d
  | [] => 0
  | (k, q) :: rest => q • FixedSystem.powerCode (data c) v k + evalAt c v rest

def zero {d : ℕ} (v : Vector d) : Bool := decide (∀ i, v i = 0)

section Semantics
variable {K : Type*} [Field K] [Algebra ℚ K] {d : ℕ}
variable (z : K) (c : Vector d) (hz : z ^ (d + 1) = decode z c)

include hz in
theorem decode_reduce (e : RationalPolynomialCode) :
    decode z (reduce c e) = Polynomial.aeval z e.polynomial := by
  induction e with
  | nil => simp [reduce, RationalPolynomialCode.polynomial]
  | cons t ts ih =>
    rcases t with ⟨k, q⟩
    rw [reduce, map_add, map_smul, decode_power z c hz, ih]
    simp only [RationalPolynomialCode.polynomial, map_add,
      Polynomial.aeval_monomial, Algebra.smul_def]

include hz in
theorem decode_powerCode (v : Vector d) (k : ℕ) :
    decode z (FixedSystem.powerCode (data c) v k) = (decode z v) ^ k := by
  induction k with
  | zero => simp [FixedSystem.powerCode, data]
  | succ k ih =>
    rw [FixedSystem.powerCode, decode_mul z c _ _ hz, ih, pow_succ]

include hz in
theorem decode_evalAt (v : Vector d) (e : RationalPolynomialCode) :
    decode z (evalAt c v e) = Polynomial.aeval (decode z v) e.polynomial := by
  induction e with
  | nil => simp [evalAt, RationalPolynomialCode.polynomial]
  | cons t ts ih =>
    rcases t with ⟨k, q⟩
    rw [evalAt, map_add, map_smul, decode_powerCode z c hz, ih]
    simp only [RationalPolynomialCode.polynomial, map_add,
      Polynomial.aeval_monomial, Algebra.smul_def]

theorem zero_sound (v : Vector d) (h : zero v = true) : decode z v = 0 := by
  simp only [zero, decide_eq_true_eq] at h
  have hv : v = 0 := funext h
  rw [hv, map_zero]

end Semantics

/-- No real/complex equality decision occurs in this checker. -/
def checkEmbedding {d : ℕ} (c : Vector d) (source : RationalBox)
    (expression : RationalPolynomialCode) (target : RootCode) : Bool :=
  zero (evalAt c (reduce c expression) target.coefficients) &&
    (RationalBox.eval source expression).inside target.rectangle

/-- A successful check identifies the original specified root, not merely
some root of the same polynomial. Valid root descriptors are mathematical
input data; no unimplemented validity test is hidden in this procedure. -/
theorem checkEmbedding_sound {d : ℕ} (c : Vector d) (source : RationalBox)
    (expression : RationalPolynomialCode) (target : RootCode)
    (θ w : ℂ) (hθ : θ ^ (d + 1) = decode θ c)
    (hsource : source.Contains θ) (htarget : target.Represents w)
    (h : checkEmbedding c source expression target = true) :
    decode θ (reduce c expression) = w := by
  simp only [checkEmbedding, Bool.and_eq_true_eq_eq_true_and_eq_true] at h
  obtain ⟨heq, hbox⟩ := h
  have he : Polynomial.aeval (decode θ (reduce c expression)) target.polynomial = 0 := by
    change Polynomial.aeval (decode θ (reduce c expression))
      target.coefficients.polynomial = 0
    rw [← decode_evalAt θ c hθ (reduce c expression) target.coefficients]
    exact zero_sound θ _ heq
  have hb : target.rectangle.Contains (decode θ (reduce c expression)) := by
    rw [decode_reduce θ c hθ]
    exact RationalBox.inside_sound hbox (RationalBox.eval_contains hsource expression)
  exact htarget.2.2.2 _ hb he

def checkFamily {d m : ℕ} (c : Vector d) (source : RationalBox)
    (expression : Fin m → RationalPolynomialCode) (target : Fin m → RootCode) : Bool :=
  decide (∀ i, checkEmbedding c source (expression i) (target i) = true)

def familyCoordinates {d m : ℕ} (c : Vector d)
    (expression : Fin m → RationalPolynomialCode) : Fin m → Vector d :=
  fun i => reduce c (expression i)

theorem checkFamily_sound {d m : ℕ} (c : Vector d) (source : RationalBox)
    (expression : Fin m → RationalPolynomialCode) (target : Fin m → RootCode)
    (θ : ℂ) (w : Fin m → ℂ) (hθ : θ ^ (d + 1) = decode θ c)
    (hsource : source.Contains θ) (htarget : ∀ i, (target i).Represents (w i))
    (h : checkFamily c source expression target = true) :
    ∀ i, decode θ (familyCoordinates c expression i) = w i := by
  simp only [checkFamily, decide_eq_true_eq] at h
  intro i
  exact checkEmbedding_sound c source (expression i) (target i) θ (w i)
    hθ hsource (htarget i) (h i)

/-- Once the candidate common embedding has actually passed the checks,
coordinate comparison decides equality of the original independently encoded
roots. This does not assume their original defining fields were equal. -/
theorem original_roots_equal_iff {d m : ℕ} (c : Vector d) (source : RationalBox)
    (expression : Fin m → RationalPolynomialCode) (target : Fin m → RootCode)
    (θ : ℂ) (w : Fin m → ℂ) (hmin : polynomial c = minpoly ℚ θ)
    (hsource : source.Contains θ) (htarget : ∀ i, (target i).Represents (w i))
    (h : checkFamily c source expression target = true) (i j : Fin m) :
    PowerArithmetic.equal (familyCoordinates c expression i) (familyCoordinates c expression j) =
      true ↔ w i = w j := by
  have hθ : θ ^ (d + 1) = decode θ c :=
    relation_of_root θ c (by rw [hmin]; exact minpoly.aeval ℚ θ)
  have hw := checkFamily_sound c source expression target θ w hθ hsource htarget h
  rw [PowerArithmetic.equal_iff θ c _ _ hmin, hw i, hw j]

end Holant.LocalDrafts.EffectiveAlgebraic.CommonFieldCheck
