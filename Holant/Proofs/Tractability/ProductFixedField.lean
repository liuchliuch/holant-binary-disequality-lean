import Holant.Proofs.Tractability.ProductEliminationBounds
import Holant.Algebraic.FiniteFamilyField
import Holant.Algebraic.FixedFamilySize


namespace Holant.LocalDrafts.Tractability.ProductElimination

open Holant.Algebraic

variable {K L : Type*} [CommSemiring K] [CommSemiring L]

def Factor.map {n : ℕ} (φ : K →+* L) : Factor K n → Factor L n
  | .scalar c => .scalar (φ c)
  | .unary j u => .unary j (fun b => φ (u b))
  | .link a b p => .link a b p

theorem Factor.map_eval {n : ℕ} (φ : K →+* L) (f : Factor K n) (x : Fin n → Bool) :
    (f.map φ).eval x = φ (f.eval x) := by
  cases f with
  | scalar c => rfl
  | unary j u => rfl
  | link a b p => simp only [Factor.map, Factor.eval]; split <;> simp

theorem weight_map {n : ℕ} (φ : K →+* L) (fs : List (Factor K n)) (x : Fin n → Bool) :
    weight (fs.map (Factor.map φ)) x = φ (weight fs x) := by
  induction fs with
  | nil => simp
  | cons f fs ih => simp [Factor.map_eval, ih]

/-- Exact naturality of the complete elimination, derived from its sum proof. -/
theorem evaluate_map {n : ℕ} (φ : K →+* L) (fs : List (Factor K n)) :
    evaluate (fs.map (Factor.map φ)) = φ (evaluate fs) := by
  rw [evaluate_eq_partition, evaluate_eq_partition]
  simp only [partition, weight_map, map_sum]

/-- All scalar leaves are addresses in a fixed finite table. Signs on links
are combinatorial Booleans and introduce only the field constants zero and one. -/
inductive LabelledFactor (A : Type*) (n : ℕ) where
  | scalar (label : A)
  | unary (port : Fin n) (labels : Bool → A)
  | link (left right : Fin n) (flip : Bool)

def LabelledFactor.realize {A : Type*} {n : ℕ} (coeff : A → K) : LabelledFactor A n → Factor K n
  | .scalar a => .scalar (coeff a)
  | .unary j a => .unary j (fun b => coeff (a b))
  | .link a b p => .link a b p

theorem realize_map {A : Type*} {n : ℕ} (φ : K →+* L) (coeff : A → K)
    (f : LabelledFactor A n) :
    (f.realize coeff).map φ = f.realize (fun a => φ (coeff a)) := by
  cases f <;> rfl

section CommonField

variable {A : Type*} [Finite A] {F : Type*} [Field F] [Algebra ℚ F]
    (coeff : A → F) (halg : ∀ a, IsAlgebraic ℚ (coeff a))

noncomputable def commonAnswer {n : ℕ} (fs : List (LabelledFactor A n)) : familyField coeff :=
  evaluate (fs.map (LabelledFactor.realize (fieldCoefficient coeff)))

theorem commonAnswer_exact {n : ℕ} (fs : List (LabelledFactor A n)) :
    (commonAnswer coeff fs : F) = evaluate (fs.map (LabelledFactor.realize coeff)) := by
  have hcoeff : (fun a => (familyField coeff).subtype (fieldCoefficient coeff a)) = coeff := by
    funext a
    rfl
  have h := evaluate_map (familyField coeff).subtype
    (fs.map (LabelledFactor.realize (fieldCoefficient coeff)))
  have hmap :
      (fs.map (LabelledFactor.realize (fieldCoefficient coeff))).map
          (Factor.map (familyField coeff).subtype) =
        fs.map (LabelledFactor.realize coeff) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro f _
    change (f.realize (fieldCoefficient coeff)).map (familyField coeff).subtype =
      f.realize coeff
    rw [realize_map, hcoeff]
  rw [hmap] at h
  calc
    (commonAnswer coeff fs : F) =
        (familyField coeff).subtype
          (evaluate (fs.map (LabelledFactor.realize (fieldCoefficient coeff)))) := rfl
    _ = evaluate (fs.map (LabelledFactor.realize coeff)) := h.symm

noncomputable def answerBits {n : ℕ} (fs : List (LabelledFactor A n)) : List Bool :=
  (familyPresentation coeff halg).encoding.encode (commonAnswer coeff fs)

/-- The answer is the unchanged field value, with a decoding-correct codec. -/
theorem answerBits_decode (halg : ∀ a, IsAlgebraic ℚ (coeff a))
    {n : ℕ} (fs : List (LabelledFactor A n)) :
    (familyPresentation coeff halg).encoding.decode (answerBits coeff halg fs) =
      some (commonAnswer coeff fs) :=
  (familyPresentation coeff halg).encoding.decode_encode _

end CommonField
end Holant.LocalDrafts.Tractability.ProductElimination
