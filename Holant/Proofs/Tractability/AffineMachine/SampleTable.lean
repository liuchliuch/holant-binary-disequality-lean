import Holant.Proofs.Tractability.AffineMachine.Reconstruction
import Mathlib.Data.Vector.Basic


namespace Holant.LocalDrafts.Tractability.AffineMachine.SampleTable

noncomputable section

open Holant.Tractable AffinePhase TwoTranslate
open scoped BigOperators

structure Samples (n : ℕ) where
  base : ZMod 4
  singles : List.Vector (ZMod 4) n
  pairs : List.Vector (List.Vector (ZMod 4) n) n

def capture {n : ℕ} (q : Word n → ZMod 4) : Samples n where
  base := q (origin n)
  singles := List.Vector.ofFn (fun j => q (basis j))
  pairs := List.Vector.ofFn (fun j => List.Vector.ofFn (fun k => q (xor (basis j) (basis k))))

def reconstruct {n : ℕ} (q : Word n → ZMod 4)
    (hq : ∀ z u v w, thirdDifference q z u v w = 0) : QuadraticPhase n :=
  let S := capture q
  { constant := S.base
    linear := fun j => S.singles.get j - S.base
    mixed := fun j k => (S.pairs.get j).get k - S.singles.get j - S.singles.get k + S.base
    even_mixed := fun j k _ => by
      simpa [S, capture, Reconstruction.mixedCoefficient] using Reconstruction.mixed_even q hq j k }

theorem reconstruct_eq {n : ℕ} (q : Word n → ZMod 4)
    (hq : ∀ z u v w, thirdDifference q z u v w = 0) :
    reconstruct q hq = Reconstruction.coefficients q hq := by
  simp [reconstruct, capture, Reconstruction.coefficients]
  funext j k
  simp only [Reconstruction.mixedCoefficient, AffinePhase.xor, Bool.xor_comm]

theorem reconstruct_eval {n : ℕ} (q : Word n → ZMod 4)
    (hq : ∀ z u v w, thirdDifference q z u v w = 0) (x : Word n) :
    (reconstruct q hq).eval x = q x := by
  rw [reconstruct_eq, Reconstruction.eval_coefficients]

def schedule (n : ℕ) : List (Word n) :=
  [origin n] ++ (List.finRange n).map basis ++
    (List.finRange n).flatMap (fun j => (List.finRange n).map (fun k => xor (basis j) (basis k)))

theorem schedule_length (n : ℕ) : (schedule n).length = 1 + n + n * n := by
  simp [schedule, List.length_flatMap]
  omega

/-- The cost is the sum over the very same finite sample schedule, not over
assignments. This generic counting lemma does not supply a bound for q itself. -/
def sampleWork {n : ℕ} (cost : Word n → ℕ) : ℕ := ((schedule n).map cost).sum

theorem sampleWork_le {n C : ℕ} (cost : Word n → ℕ) (hc : ∀ x, cost x ≤ C) :
    sampleWork cost ≤ (1 + n + n * n) * C := by
  have h (xs : List (Word n)) : (xs.map cost).sum ≤ xs.length * C := by
    induction xs with
    | nil => simp
    | cons x xs ih => simp only [List.map_cons, List.sum_cons, List.length_cons]; nlinarith [hc x]
  simpa [sampleWork, schedule_length] using h (schedule n)

def pullback {m n : ℕ} (Q : QuadraticPhase n) (p : Word m → Word n) (hp : IsAffineMap p) :
    QuadraticPhase m := reconstruct (fun x => Q.eval (p x)) (Reconstruction.precompose_third Q p hp)

@[simp] theorem pullback_eq {m n : ℕ} (Q : QuadraticPhase n) (p : Word m → Word n)
    (hp : IsAffineMap p) : pullback Q p hp = Reconstruction.pullback Q p hp :=
  reconstruct_eq _ _

def addParity {n : ℕ} (Q : QuadraticPhase n) (a : Fin n → ZMod 2) (t : ZMod 4) : QuadraticPhase n :=
  reconstruct (fun x => Q.eval x + t * bitLift (dot a x)) (by
    intro z u v w
    rw [thirdDifference_add, quadratic_thirdDifference, thirdDifference_mul_const, bitLift_dot_thirdDifference]
    simp)

@[simp] theorem addParity_eq {n : ℕ} (Q : QuadraticPhase n) (a : Fin n → ZMod 2) (t : ZMod 4) :
    addParity Q a t = Reconstruction.addParity Q a t := by
  exact reconstruct_eq _ _

end
end Holant.LocalDrafts.Tractability.AffineMachine.SampleTable
