import Holant.Proofs.BinaryInterpolation.EffectiveRecognition.CommonFieldMachine.Codec
import Mathlib.Data.List.GetD
import Mathlib.Algebra.BigOperators.Fin


namespace Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.CommonFieldMachine
open Holant.LocalDrafts.EffectiveAlgebraic Holant.Algebraic
open scoped BigOperators
namespace Coordinates

def tab {A : Type} (n : ℕ) (f : ℕ → A) : List A := (List.range n).map f
def «at» (v : List ℚ) (i : ℕ) : ℚ := v.getD i 0
def zero (n : ℕ) : List ℚ := tab n (fun _ => 0)
def unit (n : ℕ) : List ℚ := tab n (fun i => if i = 0 then 1 else 0)
def scale (q : ℚ) (v : List ℚ) : List ℚ := v.map (q * ·)
def add (n : ℕ) (u v : List ℚ) : List ℚ := tab n (fun i => «at» u i + «at» v i)
def sum (n : ℕ) (vs : List (List ℚ)) : List ℚ :=
  tab n (fun i => (vs.map (fun v => «at» v i)).sum)
def basisStep (c : List ℚ) (i : ℕ) : List ℚ :=
  if i+1 < c.length then tab c.length (fun j => if j = i+1 then 1 else 0) else c
def shift (c v : List ℚ) : List ℚ :=
  sum c.length (tab c.length (fun i => scale («at» v i) (basisStep c i)))
def power (c : List ℚ) : ℕ → List ℚ
  | 0 => unit c.length
  | k+1 => shift c (power c k)
def mul (c u v : List ℚ) : List ℚ :=
  sum c.length (tab c.length (fun i =>
    sum c.length (tab c.length (fun j => scale («at» u i * «at» v j) (power c (i+j))))))
def powerAt (c v : List ℚ) : ℕ → List ℚ
  | 0 => unit c.length
  | k+1 => mul c (powerAt c v k) v
def reduce (c : List ℚ) : RationalPolynomialCode → List ℚ
  | [] => zero c.length
  | (k,q)::ps => add c.length (scale q (power c k)) (reduce c ps)
def evalAt (c v : List ℚ) : RationalPolynomialCode → List ℚ
  | [] => zero c.length
  | (k,q)::ps => add c.length (scale q (powerAt c v k)) (evalAt c v ps)
def isZero (v : List ℚ) : Bool := v.all (fun q => decide (q = 0))

@[simp] theorem tab_length {A : Type} (n : ℕ) (f : ℕ → A) : (tab n f).length = n := by
  simp [tab]

theorem tab_ofFn {A : Type} (n : ℕ) (f : ℕ → A) :
    tab n f = List.ofFn (fun i : Fin n => f i.val) := by
  apply List.ext_getElem <;> simp [tab]

@[simp] theorem at_ofFn {n : ℕ} (v : Fin n → ℚ) (i : Fin n) :
    «at» (List.ofFn v) i.val = v i := by
  rw [«at», List.getD_eq_getElem _ _ (by simpa using i.isLt)]
  simp

@[simp] theorem zero_ofFn (n : ℕ) : zero n = List.ofFn (fun _ : Fin n => (0 : ℚ)) :=
  tab_ofFn _ _
@[simp] theorem unit_ofFn (d : ℕ) : unit (d+1) = List.ofFn (PowerArithmetic.unit d) := by
  rw [unit, tab_ofFn]
  congr 1
  funext i
  simp only [PowerArithmetic.unit, Pi.single_apply]
  by_cases h : i=0
  · subst i; simp
  · have hv : i.val ≠ 0 := fun he => h (Fin.ext he)
    simp [h,hv]
@[simp] theorem scale_ofFn {n : ℕ} (q : ℚ) (v : Fin n → ℚ) :
    scale q (List.ofFn v) = List.ofFn (q • v) := by
  rw [scale, List.map_ofFn]
  rfl
@[simp] theorem add_ofFn {n : ℕ} (u v : Fin n → ℚ) :
    add n (List.ofFn u) (List.ofFn v) = List.ofFn (u+v) := by
  simp [add, tab_ofFn]
  rfl
@[simp] theorem sum_ofFn {n m : ℕ} (v : Fin m → Fin n → ℚ) :
    sum n (List.ofFn (fun j => List.ofFn (v j))) = List.ofFn (∑ j, v j) := by
  simp [sum, tab_ofFn, List.map_ofFn, List.sum_ofFn]
  funext i
  exact (Finset.sum_apply i Finset.univ v).symm

theorem basisStep_ofFn {d : ℕ} (c : PowerArithmetic.Vector d) (i : Fin (d+1)) :
    basisStep (List.ofFn c) i.val = List.ofFn (PowerArithmetic.stepVector c i) := by
  unfold basisStep PowerArithmetic.stepVector
  simp only [List.length_ofFn]
  split_ifs with h
  · rw [tab_ofFn]
    congr 1
    funext j
    simp [Pi.single_apply, Fin.ext_iff, eq_comm]
  · rfl

theorem shift_ofFn {d : ℕ} (c v : PowerArithmetic.Vector d) :
    shift (List.ofFn c) (List.ofFn v) = List.ofFn (PowerArithmetic.shift c v) := by
  simp only [shift, List.length_ofFn, tab_ofFn, at_ofFn, basisStep_ofFn,
    scale_ofFn, sum_ofFn, PowerArithmetic.shift]

theorem power_ofFn {d : ℕ} (c : PowerArithmetic.Vector d) (k : ℕ) :
    power (List.ofFn c) k = List.ofFn (PowerArithmetic.power c k) := by
  induction k with
  | zero => simp [power, PowerArithmetic.power]
  | succ k ih => rw [power, ih, shift_ofFn, PowerArithmetic.power]

theorem mul_ofFn {d : ℕ} (c u v : PowerArithmetic.Vector d) :
    mul (List.ofFn c) (List.ofFn u) (List.ofFn v) =
      List.ofFn ((PowerArithmetic.data c).mulCode u v) := by
  simp only [mul, List.length_ofFn, tab_ofFn, at_ofFn, power_ofFn,
    scale_ofFn, sum_ofFn, ArithmeticData.mulCode, PowerArithmetic.data]

theorem powerAt_ofFn {d : ℕ} (c v : PowerArithmetic.Vector d) (k : ℕ) :
    powerAt (List.ofFn c) (List.ofFn v) k =
      List.ofFn (FixedSystem.powerCode (PowerArithmetic.data c) v k) := by
  induction k with
  | zero => simp [powerAt, FixedSystem.powerCode, PowerArithmetic.data]
  | succ k ih => rw [powerAt, ih, mul_ofFn, FixedSystem.powerCode]

theorem reduce_ofFn {d : ℕ} (c : PowerArithmetic.Vector d) (p : RationalPolynomialCode) :
    reduce (List.ofFn c) p = List.ofFn (CommonFieldCheck.reduce c p) := by
  induction p with
  | nil => simp [reduce, CommonFieldCheck.reduce]
  | cons t ps ih =>
    rcases t with ⟨k,q⟩
    simp only [reduce, CommonFieldCheck.reduce, List.length_ofFn, power_ofFn,
      scale_ofFn, ih, add_ofFn]

theorem evalAt_ofFn {d : ℕ} (c v : PowerArithmetic.Vector d) (p : RationalPolynomialCode) :
    evalAt (List.ofFn c) (List.ofFn v) p = List.ofFn (CommonFieldCheck.evalAt c v p) := by
  induction p with
  | nil => simp [evalAt, CommonFieldCheck.evalAt]
  | cons t ps ih =>
    rcases t with ⟨k,q⟩
    simp only [evalAt, CommonFieldCheck.evalAt, List.length_ofFn, powerAt_ofFn,
      scale_ofFn, ih, add_ofFn]

@[simp] theorem isZero_ofFn {d : ℕ} (v : PowerArithmetic.Vector d) :
    isZero (List.ofFn v) = CommonFieldCheck.zero v := by
  apply Bool.eq_iff_iff.mpr
  simp only [isZero, CommonFieldCheck.zero, List.all_eq_true, decide_eq_true_eq]
  constructor
  · intro h i
    exact h (v i) (List.mem_ofFn.mpr ⟨i,rfl⟩)
  · intro h x hx
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    exact h i

@[simp] theorem shift_length (c v : List ℚ) : (shift c v).length = c.length := by
  simp [shift, sum]
@[simp] theorem mul_length (c u v : List ℚ) : (mul c u v).length = c.length := by
  simp [mul, sum]
@[simp] theorem power_length (c : List ℚ) (k : ℕ) : (power c k).length = c.length := by
  cases k <;> simp [power, unit]
@[simp] theorem powerAt_length (c v : List ℚ) (k : ℕ) :
    (powerAt c v k).length = c.length := by cases k <;> simp [powerAt, unit]
@[simp] theorem reduce_length (c : List ℚ) (p : RationalPolynomialCode) :
    (reduce c p).length = c.length := by cases p <;> simp [reduce, zero, add]
@[simp] theorem evalAt_length (c v : List ℚ) (p : RationalPolynomialCode) :
    (evalAt c v p).length = c.length := by cases p <;> simp [evalAt, zero, add]

end Coordinates
end Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.CommonFieldMachine
