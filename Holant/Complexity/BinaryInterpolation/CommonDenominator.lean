import Holant.Complexity.BinaryInterpolation.NormalizedQueries

/-! One final variable reciprocal suffices for the complete interpolation
postprocessor. All intermediate numerators/denominators use only ring operations;
every denominator is nonzero by node separation and recorded nonzero scalars. -/
namespace Holant.Complexity.BinaryInterpolation
open scoped BigOperators
noncomputable section
variable {K : Type*} [Field K] {m n : ℕ}

def commonDenominator (d : Fin m→K) : K := ∏i,d i
def commonNumerator (d y : Fin m→K) : K := ∑i,y i*∏j∈Finset.univ.erase i,d j

theorem commonDenominator_ne_zero (d : Fin m→K) (hd : ∀i,d i≠0) :
    commonDenominator d≠0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hd i)

theorem sum_div_common (d y : Fin m→K) (hd : ∀i,d i≠0) :
    (∑i,y i/d i)=commonNumerator d y/commonDenominator d := by
  apply (eq_div_iff (commonDenominator_ne_zero d hd)).mpr
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  have hp : d i*(∏j∈Finset.univ.erase i,d j)=commonDenominator d :=
    Finset.mul_prod_erase Finset.univ d (Finset.mem_univ i)
  rw [←hp]
  field_simp [hd i]

def queryDenominator (nodes c : Fin (m+1)→K) (i : Fin (m+1)) : K :=
  (c i)^m*interpolationDenominator nodes i

theorem queryDenominator_ne_zero (nodes c : Fin (m+1)→K)
    (hi : Function.Injective nodes) (hc : ∀i,c i≠0) (i : Fin (m+1)) :
    queryDenominator nodes c i≠0 :=
  mul_ne_zero (pow_ne_zero _ (hc i)) (interpolationDenominator_ne_zero nodes hi i)

theorem recover_normalized_common (nodes c y : Fin (m+1)→K)
    (hi : Function.Injective nodes) (hc : ∀i,c i≠0) :
    recoverTop nodes (fun i => y i/(c i)^m)=
      commonNumerator (queryDenominator nodes c) y/commonDenominator (queryDenominator nodes c) := by
  simpa only [recoverTop,div_div,queryDenominator] using
    sum_div_common (queryDenominator nodes c) y (queryDenominator_ne_zero nodes c hi hc)

end
end Holant.Complexity.BinaryInterpolation
