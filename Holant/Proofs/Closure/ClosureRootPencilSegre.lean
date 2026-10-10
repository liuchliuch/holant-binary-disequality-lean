import Holant.Proofs.Closure.ClosureRootPencilSupport
import Holant.Proofs.Closure.ClosureRootPencilMinor
import Mathlib.Tactic.FinCases

/-! Segre equations of the whole literal pencil, derived from actual root
samples and the internally proved common support. No ruling is an input. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureRootPencil
open Holant Holant.Projective Polynomial

def bits (a b : Bool) : Fin 2 → Bool := Fin.cons a (Fin.cons b Fin.elim0)

@[simp] theorem bits_zero (a b : Bool) : bits a b 0=a := rfl
@[simp] theorem bits_one (a b : Bool) : bits a b 1=b := rfl

def coordinates {m : ℕ} {f : Signature ℂ 4} (P : Product m f)
    (q : Signature ℂ 4) : Kernel ℂ := fun a b => q (P.word (bits a b))

def determinant (M : Kernel ℂ) : ℂ :=
  M false false*M true true-M false true*M true false

theorem product_coordinates_det {m : ℕ} {f g : Signature ℂ 4}
    (P : Product m f) (E : Product m g) (supported : support f ⊆ support g) :
    determinant (coordinates P g)=0 := by
  have h := P.update_minor_of_support_subset E supported (bits false false) (bits true true) 0
  have ha : Function.update (bits false false) 0 ((bits true true) 0)=bits true false := by
    funext i
    fin_cases i <;> rfl
  have hb : Function.update (bits true true) 0 ((bits false false) 0)=bits false true := by
    funext i
    fin_cases i <;> rfl
  rw [ha,hb] at h
  unfold determinant coordinates
  rw [h,mul_comm]
  exact sub_self _

theorem root_coordinates_det {m : ℕ} (hm : 3 ≤ m) (U V : Signature ℂ 4)
    (independent : ¬ Dependent U V)
    (samples : ∀ t : ℂ, t^m=1 → pencil U V t=0 ∨ RootProduct m (pencil U V t))
    (P : Product m (pencil U V 1)) (t : ℂ) (ht : t^m=1) :
    determinant (coordinates P (pencil U V t))=0 := by
  obtain ⟨E⟩ := independent_root_supports U V independent samples t ht
  exact product_coordinates_det P E
    (independent_samples_common_support hm U V independent samples 1 t (by simp) ht).subset

/-- Quadratic interpolation proves rank one for every linear combination of
the endpoints, not merely for the finite sampled family. -/
theorem coordinates_span_det {m : ℕ} (hm : 3 ≤ m) (U V : Signature ℂ 4)
    (independent : ¬ Dependent U V)
    (samples : ∀ t : ℂ, t^m=1 → pencil U V t=0 ∨ RootProduct m (pencil U V t))
    (P : Product m (pencil U V 1)) (s t : ℂ) :
    determinant (s • coordinates P U+t • coordinates P V)=0 := by
  let A := coordinates P U
  let B := coordinates P V
  let mixed := A false false*B true true+B false false*A true true-
    A false true*B true false-B false true*A true false
  let poly : ℂ[X] :=
    (C (A false false)+C (B false false)*X)*(C (A true true)+C (B true true)*X)-
    (C (A false true)+C (B false true)*X)*(C (A true false)+C (B true false)*X)
  have linearDegree (a b : ℂ) : (C a+C b*X : ℂ[X]).natDegree ≤ 1 := by
    apply natDegree_add_le_of_degree_le
    · simp
    · simpa using natDegree_C_mul_X_pow_le b 1
  have polyZero : poly=0 := by
    apply quadratic_eq_zero_on_rootPolygon hm
    · apply (natDegree_sub_le _ _).trans
      apply max_le <;> apply natDegree_mul_le.trans
      all_goals have := linearDegree (A false false) (B false false)
      all_goals have := linearDegree (A true true) (B true true)
      all_goals have := linearDegree (A false true) (B false true)
      all_goals have := linearDegree (A true false) (B true false)
      all_goals omega
    · intro z hz
      have he := root_coordinates_det hm U V independent samples P z hz
      change (A false false+z*B false false)*(A true true+z*B true true)-
        (A false true+z*B false true)*(A true false+z*B true false)=0 at he
      simp only [poly,eval_sub,eval_mul,eval_add,eval_C,eval_X]
      linear_combination he
  have expanded : poly=C (determinant A)+C mixed*X+C (determinant B)*X^2 := by
    dsimp [poly,determinant,mixed]
    simp only [map_add,map_sub,map_mul]
    ring
  have c0 := congrArg (fun q : ℂ[X] => q.coeff 0) polyZero
  have c1 := congrArg (fun q : ℂ[X] => q.coeff 1) polyZero
  have c2 := congrArg (fun q : ℂ[X] => q.coeff 2) polyZero
  have h0 : determinant A=0 := by simpa [expanded] using c0
  have h1 : mixed=0 := by simpa [expanded] using c1
  have h2 : determinant B=0 := by simpa [expanded] using c2
  change determinant (s • A+t • B)=0
  have expansion : determinant (s • A+t • B)=
      s^2*determinant A+s*t*mixed+t^2*determinant B := by
    simp only [determinant,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    dsimp [mixed]
    ring
  rw [expansion,h0,h1,h2]
  ring

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureRootPencil
