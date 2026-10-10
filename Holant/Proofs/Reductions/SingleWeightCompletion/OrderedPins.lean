import Holant.EOCompletion
import Holant.Tractable.Criteria


noncomputable section
namespace Holant.LocalDrafts.Hardness.SingleWeightCompletion
open scoped BigOperators
variable {K : Type*} [Field K] {n : ℕ}

def extra (n d : ℕ) : ℕ := if n ≤ 2*d then 2*d-n else n-2*d
def pin (n d : ℕ) : Bool := decide (2*d < n)
def completed (f : Signature K n) (d : ℕ) : Signature K (n+extra n d) :=
  Signature.tensor f (Signature.unaryPower (Signature.pointMass (pin n d)) (extra n d))

theorem completed_exact (f : Signature K n) (d : ℕ) :
    (⟨n+extra n d,completed f d⟩ : AnySignature K) = Signature.completeToEO f d := by
  by_cases h : n ≤ 2*d
  · have hp : pin n d = false := by simp [pin, Nat.not_lt.mpr h]
    have he : extra n d = 2*d-n := ite_eq_left h
    calc
      (⟨n+extra n d,completed f d⟩ : AnySignature K) =
          ⟨n+extra n d,
            Signature.tensor f (Signature.unaryPower (Signature.pointMass false) (extra n d))⟩ := by
        simp only [completed, hp]
      _ = ⟨n+(2*d-n),Signature.completeWithZeros f d⟩ :=
        congrArg
          (fun m : ℕ => (⟨n+m,
            Signature.tensor f (Signature.unaryPower (Signature.pointMass false) m)⟩ : AnySignature K)) he
      _ = Signature.completeToEO f d := (ite_eq_left h).symm
  · have hh : 2*d < n := by omega
    have hp : pin n d = true := by simp [pin, hh]
    have he : extra n d = n-2*d := ite_eq_right h
    calc
      (⟨n+extra n d,completed f d⟩ : AnySignature K) =
          ⟨n+extra n d,
            Signature.tensor f (Signature.unaryPower (Signature.pointMass true) (extra n d))⟩ := by
        simp only [completed, hp]
      _ = ⟨n+(n-2*d),Signature.completeWithOnes f d⟩ :=
        congrArg
          (fun m : ℕ => (⟨n+m,
            Signature.tensor f (Signature.unaryPower (Signature.pointMass true) m)⟩ : AnySignature K)) he
      _ = Signature.completeToEO f d := (ite_eq_right h).symm

def extend (d : ℕ) (x : Fin n → Bool) : Fin (n+extra n d) → Bool :=
  Fin.addCases x (fun _ => pin n d)
def restrict (d : ℕ) (x : Fin (n+extra n d) → Bool) : Fin n → Bool := fun i => x (Fin.castAdd _ i)
def Pinned (d : ℕ) (x : Fin (n+extra n d) → Bool) : Prop := ∀ j, x (Fin.natAdd n j) = pin n d

/-- Finite literal pin testing, on the exact appended block. -/
instance pinnedDecidable (d : ℕ) (x : Fin (n+extra n d) → Bool) : Decidable (Pinned d x) := by
  unfold Pinned
  infer_instance

@[simp] theorem restrict_extend (d : ℕ) (x : Fin n → Bool) : restrict d (extend d x) = x := by
  funext i; simp [restrict,extend]
@[simp] theorem extend_pinned (d : ℕ) (x : Fin n → Bool) : Pinned d (extend d x) := by
  intro j; simp [Pinned,extend]
theorem extend_restrict (d : ℕ) (x : Fin (n+extra n d) → Bool) (h : Pinned d x) :
    extend d (restrict d x) = x := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [extend,restrict]
  · simpa [extend] using (h j).symm
theorem completed_apply (f : Signature K n) (d : ℕ) (x : Fin (n+extra n d) → Bool) :
    completed f d x = if Pinned d x then f (restrict d x) else 0 := by
  rw [completed,Signature.tensor_apply,Signature.unaryPower_pointMass]
  change f (restrict d x) * (if Pinned d x then (1 : K) else 0) =
    if Pinned d x then f (restrict d x) else 0
  simp only [mul_ite, mul_one, mul_zero]
@[simp] theorem completed_extend (f : Signature K n) (d : ℕ) (x : Fin n → Bool) :
    completed f d (extend d x) = f x := by rw [completed_apply]; simp
theorem pinned_of_nonzero (f : Signature K n) (d : ℕ) (x : Fin (n+extra n d) → Bool)
    (h : completed f d x ≠ 0) : Pinned d x := by
  by_contra hn
  exact h (by rw [completed_apply,if_neg hn])
theorem completed_nonzero_iff (f : Signature K n) (d : ℕ) : completed f d ≠ 0 ↔ f ≠ 0 := by
  constructor
  · intro h hz
    apply h
    funext x
    rw [completed_apply,hz]
    split <;> rfl
  · intro h hz
    apply h
    funext x
    simpa using congrFun hz (extend d x)
theorem completed_central (f : Signature K n) (d : ℕ) (h : Signature.SingleLayer f d) :
    Signature.CentralSupport (completed f d) := by
  have he := congrArg (fun f : AnySignature K => Signature.CentralSupport f.2) (completed_exact f d)
  exact he.mpr (Signature.completeToEO_central h)
theorem completed_even (f : Signature K n) (d : ℕ) : ∃ k, n+extra n d = 2*k := by
  have he : n + extra n d = (Signature.completeToEO f d).1 :=
    congrArg Sigma.fst (completed_exact f d)
  obtain ⟨k, hk⟩ := Signature.completeToEO_even f d
  exact ⟨k, he.trans hk⟩
theorem charge_extra (n d : ℕ) : 2*(d:ℤ)-n = if pin n d then -(extra n d:ℤ) else (extra n d:ℤ) := by
  by_cases h : n ≤ 2*d <;> simp [pin,extra,h] <;> omega

end Holant.LocalDrafts.Hardness.SingleWeightCompletion
