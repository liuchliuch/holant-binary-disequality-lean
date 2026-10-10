import Holant.Proofs.Hardness.EOBinaryPlaneCore
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Algebra.Polynomial.Eval.Degree

/-! Finite conjugate interpolation with an explicit source-field embedding.
The interpolation coefficients lie in the named common star-field L; the queried
power moments remain in the original field K and are only mapped K→L afterward.
No assumption that the original coefficient field is closed under conjugation,
no equality of codecs, and no use of real part as a ring hom is made. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneConjugate
open scoped BigOperators
open Polynomial
variable {K L : Type*} [Field K] [Field L] [StarRing L]

abbrev Grid (n : ℕ) := Fin 4→Fin (n+1)

def monomial (c : Fin 4→K) {n : ℕ} (powers : Grid n) : K := ∏j,c j^(powers j).val

def spectrum (into : K→+*L) (c : Fin 4→K) (n : ℕ) : Finset L := by
  classical
  exact insert 0 (Finset.univ.image fun i : Grid n=>into (monomial c i))

def polynomial (into : K→+*L) (c : Fin 4→K) (n : ℕ) : L[X] := by
  classical
  exact Lagrange.interpolate (spectrum into c n) id (fun x=>star x)

theorem eval_spectrum (into : K→+*L) (c : Fin 4→K) (n : ℕ) (x : L)
    (hx : x∈spectrum into c n) : (polynomial into c n).eval x=star x := by
  classical
  exact Lagrange.eval_interpolate_at_node _ (fun _ _ _ _ h=>h) hx

@[simp] theorem eval_zero (into : K→+*L) (c : Fin 4→K) (n : ℕ) :
    (polynomial into c n).eval 0=0 := by
  classical
  simpa only [star_zero] using eval_spectrum into c n 0 (by simp [spectrum])

@[simp] theorem coeff_zero (into : K→+*L) (c : Fin 4→K) (n : ℕ) :
    (polynomial into c n).coeff 0=0 := by
  rw [Polynomial.coeff_zero_eq_eval_zero,eval_zero]

omit [StarRing L] in
theorem spectrum_card (into : K→+*L) (c : Fin 4→K) (n : ℕ) :
    (spectrum into c n).card≤(n+1)^4+1 := by
  classical
  apply (Finset.card_insert_le _ _).trans
  have h := Finset.card_image_le (s:=Finset.univ) (f:=fun i : Grid n=>into (monomial c i))
  have hc : (Finset.univ : Finset (Grid n)).card=(n+1)^4 := by simp [Grid]
  omega

theorem degree_bound (into : K→+*L) (c : Fin 4→K) (n : ℕ) :
    (polynomial into c n).natDegree≤(n+1)^4 := by
  classical
  have hd : (polynomial into c n).degree≤((spectrum into c n).card-1 : ℕ) :=
    Lagrange.degree_interpolate_le _ (fun _ _ _ _ h=>h)
  have hn := Polynomial.natDegree_le_of_degree_le hd
  have hc := spectrum_card into c n
  omega

omit [StarRing L] in
/-- The finite spectrum is derived from the actual four coefficient labels. -/
theorem product_spectrum (into : K→+*L) (c : Fin 4→K) {n : ℕ} (labels : Fin n→Fin 4) :
    into (∏i,c (labels i))∈spectrum into c n := by
  classical
  let powers : Grid n := fun j=>⟨Fintype.card {i : Fin n // labels i=j},by
    have hh := Fintype.card_subtype_le (fun i : Fin n=>labels i=j)
    simp only [Fintype.card_fin] at hh
    omega⟩
  have hp : (∏i,c (labels i))=monomial c powers := by
    rw [←Fintype.prod_fiberwise' labels c]
    simp only [Finset.prod_const,Finset.card_univ,monomial,powers]
  rw [hp]
  apply Finset.mem_insert_of_mem
  exact Finset.mem_image.mpr ⟨powers,Finset.mem_univ _,rfl⟩

def filtered (into : K→+*L) (c : Fin 4→K) (n : ℕ) (x : L) : L :=
  ∑k ∈ Finset.range (polynomial into c n).natDegree,
    (polynomial into c n).coeff (k+1)*x^(k+1)

theorem filtered_eval (into : K→+*L) (c : Fin 4→K) (n : ℕ) (x : L) :
    filtered into c n x=(polynomial into c n).eval x := by
  rw [Polynomial.eval_eq_sum_range,Finset.sum_range_succ']
  simp [filtered]

/-- Exact linear combination of positive-power original-field moments. This is
an algebraic identity; it does not package unproved physical query programmes. -/
theorem conjugate_moments {A : Type*} [Fintype A] (into : K→+*L) (c : Fin 4→K)
    (n : ℕ) (base : A→K) (labels : A→Fin n→Fin 4) :
    (∑x,into (base x)*star (into (∏i,c (labels x i))))=
      ∑k ∈ Finset.range (polynomial into c n).natDegree,
        (polynomial into c n).coeff (k+1)*
          into (∑x,base x*(∏i,c (labels x i))^(k+1)) := by
  classical
  simp_rw [map_sum,map_mul,map_pow,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [←eval_spectrum into c n _ (product_spectrum into c (labels x)),←filtered_eval]
  unfold filtered
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneConjugate
