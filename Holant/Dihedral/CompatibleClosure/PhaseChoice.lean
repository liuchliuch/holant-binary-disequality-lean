import Holant.Dihedral.CompatibleClosure.Monomial
import Holant.Projective.CyclicPhasePencil.Algebraic

/-! Two actual affine traces exclude at most two of the full finite root grid.
The chosen phase is algebraic and its physical representative scalar is kept. -/
noncomputable section
namespace Holant.Dihedral.CompatibleClosure
open Holant Holant.Marked

private theorem complex_root_of_mem {m : ℕ} [NeZero m] {z : ℂ}
    (hz : z ∈ Laurent.rootCoset m 1) : z^m=1 := by
  obtain ⟨u,hu⟩ := (Laurent.mem_rootCoset m 1 z).mp hz
  have h := u.property
  rw [mem_rootsOfUnity] at h
  have hh := congrArg Units.val h
  have he : (u.val : ℂ)=z := by simpa using hu
  simpa only [Units.val_pow_eq_pow_val,Units.val_one,he] using hh

/-- No phase enumeration is supplied: the complete source root grid has m
points, and only the two literal affine zeros are removed. -/
theorem simultaneous_phase {m : ℕ} (hm : 3 ≤ m) (a b : Scalar)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ t : Scalar, Roots m t ∧ 1+a*t ≠ 0 ∧ 1+b*t ≠ 0 := by
  classical
  letI : NeZero m := ⟨by omega⟩
  let bad : Finset ℂ := {-1/(a:ℂ),-1/(b:ℂ)}
  have hc : bad.card < (Laurent.rootCoset m 1).card := by
    rw [Laurent.card_rootCoset]
    have hbcard : bad.card ≤ 2 := by
      simpa only [bad,Finset.card_singleton] using Finset.card_insert_le (-1/(a:ℂ)) ({-1/(b:ℂ)} : Finset ℂ)
    omega
  obtain ⟨z,hz,hbad⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
  have hzpow := complex_root_of_mem hz
  let t : Scalar := Projective.CyclicPhasePencil.algebraicRoot (by omega) z hzpow
  have ha' : (a:ℂ) ≠ 0 := by exact_mod_cast ha
  have hb' : (b:ℂ) ≠ 0 := by exact_mod_cast hb
  refine ⟨t,Projective.CyclicPhasePencil.algebraicRoot_pow (by omega) z hzpow,?_,?_⟩
  · intro hh
    have hh' : 1+(a:ℂ)*z=0 := by
      change (1 : ℂ)+(a:ℂ)*(t:ℂ)=0
      exact_mod_cast hh
    have he : z = -1/(a:ℂ) := by apply (eq_div_iff ha').mpr; linear_combination hh'
    apply hbad
    simp only [bad,Finset.mem_insert,Finset.mem_singleton]
    exact Or.inl he
  · intro hh
    have hh' : 1+(b:ℂ)*z=0 := by
      change (1 : ℂ)+(b:ℂ)*(t:ℂ)=0
      exact_mod_cast hh
    have he : z = -1/(b:ℂ) := by apply (eq_div_iff hb').mpr; linear_combination hh'
    apply hbad
    simp only [bad,Finset.mem_insert,Finset.mem_singleton]
    exact Or.inr he

theorem trace_scale (c d : Scalar) (A B : Mat) :
    trace (scale c A) (scale d B) = (c*d)*trace A B := by
  simp only [trace,scale,Fintype.sum_bool]
  ring

/-- The same ordered actual group representative closes both compatible
factors, with every original and representative multiplier included. -/
theorem simultaneous_actual_trace {m : ℕ} (hm : 3 ≤ m) (α : Bool)
    (a b c₀ c₁ : Scalar) (ha : a ≠ 0) (hb : b ≠ 0) (hc₀ : c₀ ≠ 0) (hc₁ : c₁ ≠ 0)
    (representative : Scalar → Mat) (multiplier : Scalar → Scalar)
    (hrep : ∀ t, Roots m t → representative t = scale (multiplier t) (M α t))
    (hmul : ∀ t, Roots m t → multiplier t ≠ 0) :
    ∃ t : Scalar, Roots m t ∧ representative t ∈ groupM m ∧
      trace (scale c₀ (M α a)) (representative t) = c₀*multiplier t*(1+a*t) ∧
      trace (scale c₁ (M α b)) (representative t) = c₁*multiplier t*(1+b*t) ∧
      trace (scale c₀ (M α a)) (representative t) ≠ 0 ∧
      trace (scale c₁ (M α b)) (representative t) ≠ 0 := by
  obtain ⟨t,ht,h₀,h₁⟩ := simultaneous_phase hm a b ha hb
  have he₀ : trace (scale c₀ (M α a)) (representative t) = c₀*multiplier t*(1+a*t) := by
    rw [hrep t ht,trace_scale,trace_M]
  have he₁ : trace (scale c₁ (M α b)) (representative t) = c₁*multiplier t*(1+b*t) := by
    rw [hrep t ht,trace_scale,trace_M]
  refine ⟨t,ht,?_,he₀,he₁,?_,?_⟩
  · rw [hrep t ht]
    exact (groupM_is_group (by omega)).scale_mem _ (M_mem_group (by omega) α ht) _ (hmul t ht)
  · rw [he₀]
    exact mul_ne_zero (mul_ne_zero hc₀ (hmul t ht)) h₀
  · rw [he₁]
    exact mul_ne_zero (mul_ne_zero hc₁ (hmul t ht)) h₁

end Holant.Dihedral.CompatibleClosure
