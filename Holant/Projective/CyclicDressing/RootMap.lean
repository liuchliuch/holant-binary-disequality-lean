import Holant.Projective.CyclicQuaternary.PhysicalSource

/-! Exact image and odd-order bijectivity of the four-root dressing map from
manuscript Lemma 7.3. All roots and the square witness live in the actual
algebraic-complex field; no unrestricted complex square root is substituted. -/
noncomputable section
namespace Holant.Projective.CyclicDressing
open CyclicPhasePencil CyclicQuaternary.Physical

abbrev Roots (m : ℕ) := Fin 4 → Root m

def rootMul {m : ℕ} (a b : Root m) : Root m :=
  ⟨a.val*b.val,by rw [mul_pow,a.property,b.property,mul_one]⟩
def rootDiv {m : ℕ} (a b : Root m) : Root m :=
  ⟨a.val/b.val,by rw [div_pow,a.property,b.property,div_one]⟩
def rootPow {m : ℕ} (a : Root m) (k : ℕ) : Root m :=
  ⟨a.val^k,by rw [← pow_mul,mul_comm, pow_mul,a.property,one_pow]⟩

def dressingMap {m : ℕ} (r : Roots m) : Roots m :=
  ![rootMul (rootMul (rootMul (r 0) (r 1)) (r 2)) (r 3),
    rootMul (r 0) (r 1),rootMul (r 0) (r 2),rootMul (r 0) (r 3)]

def ratio {m : ℕ} (t : Roots m) : Root m := rootDiv (rootMul (rootMul (t 1) (t 2)) (t 3)) (t 0)

def SquareTarget {m : ℕ} (t : Roots m) : Prop :=
  ∃ z : Root m, z.val^2=(t 1).val*(t 2).val*(t 3).val/(t 0).val

/-- Necessity retains exactly the first port's phase as the square root. -/
theorem image_ratio {m : ℕ} (hm : 0<m) (r : Roots m) :
    (ratio (dressingMap r)).val=(r 0).val^2 := by
  have h0 := root_ne_zero hm (r 0).property
  have h1 := root_ne_zero hm (r 1).property
  have h2 := root_ne_zero hm (r 2).property
  have h3 := root_ne_zero hm (r 3).property
  dsimp [ratio,dressingMap,rootMul,rootDiv]
  field_simp

/-- A square witness in mu_m determines all four required original port phases. -/
def preimage {m : ℕ} (t : Roots m) (z : Root m) : Roots m :=
  ![z,rootDiv (t 1) z,rootDiv (t 2) z,rootDiv (t 3) z]

theorem dressingMap_preimage {m : ℕ} (hm : 0<m) (t : Roots m) (z : Root m)
    (hz : z.val^2=(ratio t).val) : dressingMap (preimage t z)=t := by
  have hz0 := root_ne_zero hm z.property
  have ht0 := root_ne_zero hm (t 0).property
  have he : z.val^2*(t 0).val=(t 1).val*(t 2).val*(t 3).val := (eq_div_iff ht0).mp hz
  funext i
  apply Subtype.ext
  fin_cases i
  · change z.val*((t 1).val/z.val)*((t 2).val/z.val)*((t 3).val/z.val)=(t 0).val
    calc
      _ = ((t 1).val*(t 2).val*(t 3).val)/(z.val^2) := by field_simp <;> ring
      _ = (t 0).val := (div_eq_iff (pow_ne_zero 2 hz0)).mpr (by rw [← he]; ring)
  · exact mul_div_cancel₀ _ hz0
  · exact mul_div_cancel₀ _ hz0
  · exact mul_div_cancel₀ _ hz0

/-- Exact source image criterion, for both even and odd cyclic orders. -/
theorem dressingMap_image_iff {m : ℕ} (hm : 0<m) (t : Roots m) :
    (∃ r : Roots m, dressingMap r=t) ↔ SquareTarget t := by
  constructor
  · rintro ⟨r,rfl⟩
    exact ⟨r 0,(image_ratio hm r).symm⟩
  · rintro ⟨z,hz⟩
    exact ⟨preimage t z,dressingMap_preimage hm t z hz⟩

/-- For odd order, squaring has the explicit inverse exponent (m+1)/2. -/
theorem odd_square_recover {m k : ℕ} (hm : m=2*k+1) (z : Root m) :
    (z.val^2)^(k+1)=z.val := by
  rw [← pow_mul]
  have he : 2*(k+1)=m+1 := by omega
  rw [he,pow_succ,z.property,one_mul]

theorem odd_square_root {m k : ℕ} (hm : m=2*k+1) (z : Root m) :
    (rootPow z (k+1)).val^2=z.val := by
  change (z.val^(k+1))^2=z.val
  rw [← pow_mul,mul_comm, pow_mul,odd_square_recover hm z]

/-- Equal target data and equal first phases determine the other three phases. -/
theorem dressingMap_injective_of_square {m : ℕ} (hm : 0<m)
    (hsquare : ∀ a b : Root m, a.val^2=b.val^2 → a=b) : Function.Injective (@dressingMap m) := by
  intro r s h
  have hroot : r 0=s 0 := by
    apply hsquare
    rw [← image_ratio hm r,← image_ratio hm s,h]
  have hn := root_ne_zero hm (r 0).property
  funext i
  have hi := congrArg (fun t : Roots m => (t i).val) h
  fin_cases i
  · exact hroot
  all_goals apply Subtype.ext
  all_goals change (r 0).val*_=(s 0).val*_ at hi
  all_goals rw [← hroot] at hi
  all_goals exact mul_left_cancel₀ hn hi

/-- Full source bijectivity for every odd finite cyclic order. -/
theorem dressingMap_bijective_odd {m : ℕ} (hm : Odd m) : Function.Bijective (@dressingMap m) := by
  obtain ⟨k,hk⟩ := hm
  have hm0 : 0<m := by omega
  constructor
  · apply dressingMap_injective_of_square hm0
    intro a b hab
    apply Subtype.ext
    have h := congrArg (fun z : Scalar => z^(k+1)) hab
    simpa only [odd_square_recover hk a,odd_square_recover hk b] using h
  · intro t
    exact ⟨preimage t (rootPow (ratio t) (k+1)),
      dressingMap_preimage hm0 t _ (odd_square_root hk (ratio t))⟩

end Holant.Projective.CyclicDressing
