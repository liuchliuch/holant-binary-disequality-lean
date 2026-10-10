import Holant.Proofs.Algorithms.CyclicBoundary.ZeroEndpointJoin
import Holant.Projective.CyclicQuaternary.Physical


namespace Holant.LocalDrafts.MainChain.CyclicBoundary.ZeroEndpointDressing
open Holant.Projective.CyclicQuaternary
open ZeroEndpointFactor ZeroEndpointJoin
noncomputable section

def phases (a : Fin 3 → ℂ) (i : Fin 3) : Fin 4 → ℂ :=
  ![1,1,-(a (other₁ i) / a i),a (other₂ i) / a i]

def dress (q : Signature ℂ 4) (s : Fin 4 → ℂ) : Signature ℂ 4 :=
  fun x => q x * ∏ j, (s j)^(if x j then 1 else 0)

def commonMiddle (r a : Fin 3 → ℂ) (i : Fin 3) : ℂ :=
  (a (other₁ i)*a (other₂ i)/a i) *
    (ZeroEndpointFactor.weight r a (other₁ i)-ZeroEndpointFactor.weight r a (other₂ i))

def matched (e d : ℂ) : Signature ℂ 4 :=
  ofCoordinates e e ![(0,0),(d,d),(0,0)]

/-- Both inactive and active selected blocks use the same four root phases.
In particular, this construction never divides by a block amplitude r i. -/
theorem dress_join (r a : Fin 3 → ℂ) (i : Fin 3) (ha : a i ≠ 0) :
    dress (join r a i).denote (phases a i) =
      matched (endpoint₀ r a i) (commonMiddle r a i) := by
  rw [join_denote]
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [dress, phases, matched, ofCoordinates, Fin.prod_univ_succ,
      endpoint₀, endpoint₁, middle₀, middle₁, commonMiddle, h0,h1,h2,h3]
  all_goals field_simp [ha]
  all_goals ring

theorem phases_are_roots (a : Fin 3 → ℂ) (i : Fin 3) {N : ℕ}
    (hN : Even N) (ha : ∀ k, (a k)^N = 1) :
    ∀ j, (phases a i j)^N = 1 := by
  intro j
  fin_cases j <;> simp [phases, hN.neg_pow, div_pow, ha]

theorem phases_nonzero (a : Fin 3 → ℂ) (ha : ∀ k, a k ≠ 0) (i : Fin 3) :
    ∀ j, phases a i j ≠ 0 := by
  intro j
  fin_cases j <;> simp [phases,ha]

theorem common_sum (r a : Fin 3 → ℂ) (i : Fin 3) (ha : a i ≠ 0) :
    endpoint₀ r a i + commonMiddle r a i =
      (a (other₁ i)*a (other₂ i)/a i) *
        (ZeroEndpointFactor.weight r a (other₁ i)-ZeroEndpointFactor.weight r a (other₂ i)-ZeroEndpointFactor.weight r a i) := by
  unfold endpoint₀ commonMiddle ZeroEndpointFactor.weight
  field_simp [ha]
  ring

theorem common_sum_ne_zero (r a : Fin 3 → ℂ) (ha : ∀ k, a k ≠ 0)
    (i : Fin 3) (hd : delta r a i ≠ 0) :
    endpoint₀ r a i + commonMiddle r a i ≠ 0 := by
  rw [common_sum r a i (ha i)]
  apply mul_ne_zero (div_ne_zero (mul_ne_zero (ha _) (ha _)) (ha _))
  intro hz
  apply hd
  unfold delta ZeroEndpointMinors.minor
  rw [sub_eq_zero.mp hz,sub_self]

theorem common_difference (r a : Fin 3 → ℂ) (i : Fin 3) (ha : a i ≠ 0) :
    endpoint₀ r a i - commonMiddle r a i =
      -(a (other₁ i)*a (other₂ i)/a i) *
        (ZeroEndpointFactor.weight r a (other₁ i)-ZeroEndpointFactor.weight r a (other₂ i)+ZeroEndpointFactor.weight r a i) := by
  unfold endpoint₀ commonMiddle ZeroEndpointFactor.weight
  field_simp [ha]
  ring

theorem common_difference_ne_zero (r a : Fin 3 → ℂ) (ha : ∀ k, a k ≠ 0)
    (i : Fin 3) (hd : delta r a i ≠ 0) :
    endpoint₀ r a i - commonMiddle r a i ≠ 0 := by
  rw [common_difference r a i (ha i)]
  apply mul_ne_zero (neg_ne_zero.mpr (div_ne_zero (mul_ne_zero (ha _) (ha _)) (ha _)))
  intro hz
  apply hd
  have he : ZeroEndpointFactor.weight r a (other₁ i)-ZeroEndpointFactor.weight r a (other₂ i) = -ZeroEndpointFactor.weight r a i := by
    linear_combination hz
  unfold delta ZeroEndpointMinors.minor
  rw [he]
  ring

def hadamard : Kernel ℂ := fun u v => if u && v then -1 else 1
def physical (q : Signature ℂ 4) : Signature ℂ 4 :=
  Signature.coordinateAction (fun _ => hadamard) q

theorem sum_words (f : (Fin 4 → Bool) → ℂ) :
    (∑ x, f x) = ∑ a : Bool, ∑ b : Bool, ∑ c : Bool, ∑ d : Bool, f ![a,b,c,d] := by
  rw [← Physical.words4.symm.sum_comp]
  simp only [Fintype.sum_prod_type]
  rfl

/-- The complete physical table, not just its two endpoints. -/
theorem physical_matched (e d : ℂ) :
    physical (matched e d) = ofCoordinates (2*(e+d)) (2*(e+d))
      ![(2*(e-d),2*(e-d)),(2*(e+d),2*(e+d)),(2*(e-d),2*(e-d))] := by
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [physical, Signature.coordinateAction, sum_words, matched, ofCoordinates,
      hadamard, Fin.prod_univ_succ, h0,h1,h2,h3] <;> ring

theorem physical_endpoint₀ (e d : ℂ) :
    physical (matched e d) (fun _ => false) = 2*(e+d) := by
  simp [physical, Signature.coordinateAction, sum_words, matched, ofCoordinates,
    hadamard, Fin.prod_univ_succ]
  ring

theorem physical_endpoint₁ (e d : ℂ) :
    physical (matched e d) (fun _ => true) = 2*(e+d) := by
  simp [physical, Signature.coordinateAction, sum_words, matched, ofCoordinates,
    hadamard, Fin.prod_univ_succ]
  ring

/-- Exact inverse-Walsh tensor endpoints, without assuming an amplitude is
nonzero. The sole nonvanishing condition is the explicitly computed minor. -/
theorem endpoints_nondegenerate (r a : Fin 3 → ℂ) (ha : ∀ k, a k ≠ 0)
    (i : Fin 3) (hd : delta r a i ≠ 0) :
    physical (dress (join r a i).denote (phases a i)) (fun _ => false) ≠ 0 ∧
    physical (dress (join r a i).denote (phases a i)) (fun _ => true) ≠ 0 := by
  rw [dress_join r a i (ha i),physical_endpoint₀,physical_endpoint₁]
  have h := mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) (common_sum_ne_zero r a ha i hd)
  exact ⟨h,h⟩

end
end Holant.LocalDrafts.MainChain.CyclicBoundary.ZeroEndpointDressing
