import Holant.Complexity.BinaryInterpolation.WeightFormulas

namespace Holant.Complexity.BinaryInterpolation
namespace RingFormula
variable {A : Type*}

theorem size_prodList_le (ps : List (RingFormula A)) (B : ℕ)
    (h : ∀p∈ps,p.size≤B) : (prodList ps).size≤ps.length*(B+1)+1 := by
  induction ps with
  | nil => simp [prodList,size]
  | cons p ps ih =>
    have hp := h p (by simp)
    have ht := ih (fun q hq => h q (by simp [hq]))
    simp only [prodList,size,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

theorem size_without_le {m : ℕ} (p : Fin m→RingFormula A) (i : Fin m) (B : ℕ)
    (hB : 1≤B) (hp : ∀j,(p j).size≤B) : (without p i).size≤m*(B+1)+1 := by
  unfold without
  have h := size_prodList_le (List.ofFn (fun j => if j=i then one else p j)) B ?_
  · simpa using h
  · intro q hq
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hq
    split_ifs
    · exact hB
    · exact hp j

end RingFormula
namespace WeightFormulas
open RingFormula

theorem node_size (geometric : Bool) (t : ℕ) : (node geometric t).size=2*t+1 := by
  cases geometric <;> simp [node,size_power,size_sumList,size,List.sum_replicate,Nat.mul_comm]

def denominatorSize (m : ℕ) : ℕ := 2*((m+1)*m)+(m+1)*(4*m+10)+3
def weightSize (m : ℕ) : ℕ := (m+1)*(denominatorSize m+1)+1

theorem denominator_size_le (geometric : Bool) (m : ℕ) (i : Fin (m+1)) :
    (denominator geometric m i).size≤denominatorSize m := by
  have hi : i.val+1≤m+1 := i.isLt
  have hb := size_without_le
    (fun j : Fin (m+1) => add (node geometric (i.val+1))
      (mul (literal 2) (node geometric (j.val+1)))) i (4*m+9) (by omega) ?_
  · have hm := Nat.mul_le_mul_right m hi
    simp only [denominator,size,size_power] at *
    unfold denominatorSize
    nlinarith
  · intro j
    have hj : j.val+1≤m+1 := j.isLt
    simp only [size,node_size]
    omega

theorem weight_size_le (geometric : Bool) (m : ℕ) (i : Fin (m+1)) :
    (weight geometric m i).size≤weightSize m := by
  apply size_without_le
  · unfold denominatorSize;omega
  · exact denominator_size_le geometric m

theorem totalDenominator_size_le (geometric : Bool) (m : ℕ) :
    (totalDenominator geometric m).size≤weightSize m := by
  have h := size_prodList_le (List.ofFn (denominator geometric m)) (denominatorSize m) ?_
  · simpa [totalDenominator,weightSize] using h
  · intro p hp
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp
    exact denominator_size_le geometric m i

end WeightFormulas
end Holant.Complexity.BinaryInterpolation
