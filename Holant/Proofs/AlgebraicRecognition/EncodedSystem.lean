import Holant.Proofs.AlgebraicRecognition.CommonFieldCheck


namespace Holant.LocalDrafts.EffectiveAlgebraic.EncodedSystem
open PowerArithmetic CommonFieldCheck
open scoped BigOperators

abbrev Term (m n : ℕ) := Fin m × (Fin n → ℕ)
abbrev Equation (m n : ℕ) := List (Term m n)
abbrev System (m n : ℕ) := List (Equation m n)

def materialize {d m n : ℕ} (coeff : Fin m → Vector d) (e : Equation m n) :
    FixedSystem.Equation (d + 1) n := e.map (fun t => (coeff t.1, t.2))

noncomputable def polynomial {m n : ℕ} (w : Fin m → ℂ) :
    Equation m n → MvPolynomial (Fin n) ℂ
  | [] => 0
  | t :: rest =>
    MvPolynomial.C (w t.1) * (∏ i, MvPolynomial.X i ^ t.2 i) + polynomial w rest

def check {d m n : ℕ} (c : Vector d) (source : RationalBox)
    (expression : Fin m → RationalPolynomialCode) (target : Fin m → RootCode)
    (S : System m n) (x : Fin n → Vector d) : Bool :=
  checkFamily c source expression target &&
    FixedSystem.checkSystem (data c) (S.map (materialize (familyCoordinates c expression))) x

private theorem decode_product {d n : ℕ} (θ : ℂ) (c : Vector d)
    (hθ : θ ^ (d + 1) = decode θ c) (v : Fin n → Vector d) :
    decode θ (FixedSystem.productCode (data c) n v) = ∏ i, decode θ (v i) := by
  induction n with
  | zero => simp [FixedSystem.productCode, data]
  | succ n ih =>
    rw [FixedSystem.productCode, PowerArithmetic.decode_mul θ c _ _ hθ,
      ih, Fin.prod_univ_succ]
    rfl

private theorem decode_materialize {d m n : ℕ} (θ : ℂ) (c : Vector d)
    (hθ : θ ^ (d + 1) = decode θ c) (coeff : Fin m → Vector d)
    (w : Fin m → ℂ) (hc : ∀ i, decode θ (coeff i) = w i)
    (x : Fin n → Vector d) (e : Equation m n) :
    decode θ (FixedSystem.evalEquation (data c) x (materialize coeff e)) =
      MvPolynomial.aeval (fun i => decode θ (x i)) (polynomial w e) := by
  have ht (t : Term m n) :
      decode θ (FixedSystem.evalTerm (data c) x (coeff t.1, t.2)) =
        w t.1 * ∏ i, (decode θ (x i)) ^ t.2 i := by
    unfold FixedSystem.evalTerm
    rw [PowerArithmetic.decode_mul θ c _ _ hθ, hc,
      decode_product θ c hθ]
    simp only [CommonFieldCheck.decode_powerCode θ c hθ]
  induction e with
  | nil => simp [materialize, FixedSystem.evalEquation, polynomial]
  | cons t ts ih =>
    change decode θ (FixedSystem.evalTerm (data c) x (coeff t.1,t.2) +
      FixedSystem.evalEquation (data c) x (materialize coeff ts)) = _
    rw [map_add,ht,ih]
    simp [polynomial]

theorem check_sound {d m n : ℕ} (c : Vector d) (source : RationalBox)
    (expression : Fin m → RationalPolynomialCode) (target : Fin m → RootCode)
    (S : System m n) (x : Fin n → Vector d) (θ : ℂ) (w : Fin m → ℂ)
    (hθ : θ ^ (d + 1) = decode θ c) (hsource : source.Contains θ)
    (htarget : ∀ i, (target i).Represents (w i))
    (h : check c source expression target S x = true) :
    ∀ e ∈ S, MvPolynomial.aeval (fun i => decode θ (x i)) (polynomial w e) = 0 := by
  simp only [check, Bool.and_eq_true_eq_eq_true_and_eq_true] at h
  obtain ⟨hfamily, hsystem⟩ := h
  have hc := checkFamily_sound c source expression target θ w hθ hsource htarget hfamily
  simp only [FixedSystem.checkSystem, List.all_eq_true, decide_eq_true_eq] at hsystem
  intro e he
  have hz := hsystem (materialize (familyCoordinates c expression) e)
    (List.mem_map.mpr ⟨e, he, rfl⟩)
  rw [← decode_materialize θ c hθ _ w hc x e]
  have hz' : FixedSystem.evalEquation (data c) x
      (materialize (familyCoordinates c expression) e) = 0 := funext hz
  rw [hz', map_zero]

end Holant.LocalDrafts.EffectiveAlgebraic.EncodedSystem
