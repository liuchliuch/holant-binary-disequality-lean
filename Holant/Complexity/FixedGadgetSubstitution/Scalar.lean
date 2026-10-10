import Holant.Complexity.FixedGadgetSubstitution.Raw
import Holant.Complexity.FixedGadgetSubstitution.FiniteSemantics

/-! The exact projective correction exponent is the number of distinguished
signature occurrences in the original serialized network. -/
namespace Holant.Complexity.FixedGadgetSubstitution
open scoped BigOperators
variable {K : Type*} [CommSemiring K]

 theorem list_scale_product (label : ℕ) (c : K) (rows : List RawVertex) :
    (rows.map (fun row => if row.1 = label then c else 1)).prod =
      c ^ (rows.filter (fun row => row.1 == label)).length := by
  induction rows with
  | nil => simp
  | cons row rows ih =>
    by_cases h : row.1 = label
    · simp [h,ih,pow_succ,mul_comm]
    · simp [h,ih]

 theorem scale_product (label : ℕ) (c : K) (r : RawClosedNetwork) :
    (∏ v : Fin r.vertices.length, if (r.vertices.get v).1 = label then c else 1) =
      c ^ occurrences label r := by
  rw [←List.prod_ofFn]
  have h := List.ofFn_getElem_eq_map r.vertices
    (fun row : RawVertex => if row.1 = label then c else (1 : K))
  simp only [List.get_eq_getElem]
  rw [h]
  exact list_scale_product label c r.vertices

 theorem correction {K : Type*} [Field K] (c z : K) (hc : c ≠ 0) (n : ℕ) :
    (c⁻¹)^n*(c^n*z)=z := by
  rw [←mul_assoc,←mul_pow,inv_mul_cancel₀ hc,one_pow,one_mul]

end Holant.Complexity.FixedGadgetSubstitution
