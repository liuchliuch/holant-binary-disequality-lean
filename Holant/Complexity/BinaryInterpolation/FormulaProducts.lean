import Holant.Complexity.BinaryInterpolation.RingFormula
import Holant.Complexity.BinaryInterpolation.CommonDenominator

namespace Holant.Complexity.BinaryInterpolation.RingFormula
open scoped BigOperators
variable {A K : Type*}

def power (p : RingFormula A) : ℕ→RingFormula A
  | 0 => .one
  | k+1 => .mul p (power p k)

def sumList : List (RingFormula A)→RingFormula A
  | [] => .zero
  | p::ps => .add p (sumList ps)

def prodList : List (RingFormula A)→RingFormula A
  | [] => .one
  | p::ps => .mul p (prodList ps)

theorem size_power (p : RingFormula A) (k : ℕ) : (p.power k).size=k*(p.size+1)+1 := by
  induction k with
  | zero => simp [power,size]
  | succ k ih => simp only [power,size,ih,Nat.add_mul,Nat.one_mul]; omega

theorem size_prodList (ps : List (RingFormula A)) :
    (prodList ps).size=(ps.map (fun p => p.size+1)).sum+1 := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [prodList,size,ih]; omega

theorem size_sumList (ps : List (RingFormula A)) :
    (sumList ps).size=(ps.map (fun p => p.size+1)).sum+1 := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [sumList,size,ih]; omega

variable [CommSemiring K]

@[simp] theorem eval_power (p : RingFormula A) (k : ℕ) (coeff : A→K) :
    (p.power k).eval coeff=(p.eval coeff)^k := by
  induction k with
  | zero => simp [power,eval]
  | succ k ih => simp [power,eval,ih,pow_succ,mul_comm]

@[simp] theorem eval_prodList (ps : List (RingFormula A)) (coeff : A→K) :
    (prodList ps).eval coeff=(ps.map (eval coeff)).prod := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [prodList,eval,ih]

@[simp] theorem eval_sumList (ps : List (RingFormula A)) (coeff : A→K) :
    (sumList ps).eval coeff=(ps.map (eval coeff)).sum := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [sumList,eval,ih]

def without {m : ℕ} (p : Fin m→RingFormula A) (i : Fin m) : RingFormula A :=
  prodList (List.ofFn (fun j => if j=i then .one else p j))

theorem product_skip {m : ℕ} (f : Fin m→K) (i : Fin m) :
    (∏j,if j=i then 1 else f j)=∏j∈Finset.univ.erase i,f j := by
  have h := Finset.prod_erase_mul Finset.univ (fun j => if j=i then 1 else f j)
    (Finset.mem_univ i)
  simp only [ite_true,mul_one] at h
  rw [←h]
  apply Finset.prod_congr rfl
  intro j hj
  exact if_neg (Finset.mem_erase.mp hj).1

@[simp] theorem eval_without {m : ℕ} (p : Fin m→RingFormula A)
    (i : Fin m) (coeff : A→K) :
    (without p i).eval coeff=∏j∈Finset.univ.erase i,(p j).eval coeff := by
  simp only [without,eval_prodList,List.map_ofFn,Fin.prod_ofFn,Function.comp_apply]
  have he : (fun j => eval coeff (if j=i then .one else p j))=
      (fun j => if j=i then 1 else (p j).eval coeff) := by
    funext j
    split_ifs <;> rfl
  rw [he]
  exact product_skip _ i

end Holant.Complexity.BinaryInterpolation.RingFormula
