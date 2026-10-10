import Holant.Platonic.FixedMatchingRuling.SegreCoordinates

/-! Linear spaces in a general Segre cone are contained in one ruling. -/
noncomputable section
namespace Holant.Platonic.FixedMatchingRuling.Segre
open scoped BigOperators
open Function
variable {M : Type*} [Fintype M] {κ : M → Type*}
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- A coordinate basis tensor. -/
def delta (p : (e : M) → κ e) : Array κ := by
  classical
  exact fun x => if x = p then 1 else 0

/-- Polarization of a homogeneous quadratic identity for two linear forms. -/
theorem cross_zero_of_pointwise_product (L R : V →ₗ[ℂ] ℂ)
    (h : ∀ v, L v * R v = 0) (v w : V) : L v * R w + L w * R v = 0 := by
  have hv := h v
  have hw := h w
  have hvw := h (v + w)
  simp only [map_add] at hvw
  linear_combination hvw - hv - hw

/-- A linear family through a coordinate basis tensor has no coefficients
in positions that differ from the base in two or more factors. -/
theorem two_changes_zero [DecidableEq M] (Φ : V →ₗ[ℂ] Array κ)
    (h : ∀ v, MinorsVanish (Φ v)) (v₀ : V) (p : (e : M) → κ e)
    (hbase : Φ v₀ = delta p) (v : V) (x : (e : M) → κ e)
    (e f : M) (hef : e ≠ f) (he : x e ≠ p e) (hf : x f ≠ p f) :
    Φ v x = 0 := by
  classical
  have hx : x ≠ p := fun hh => he (congrFun hh e)
  have hx' : update x e (p e) ≠ p := by
    intro hh
    have hhf := congrFun hh f
    rw [update_of_ne (Ne.symm hef)] at hhf
    exact hf hhf
  have hp' : update p e (x e) ≠ p := by
    intro hh
    have hhe := congrFun hh e
    simp only [update_self] at hhe
    exact he hhe
  have hv := h v e x p
  have hvb := h (v + v₀) e x p
  simp only [map_add, Pi.add_apply, hbase, delta, ite_eq_right hx, ite_eq_right hx',
    ite_eq_right hp', ite_true, add_zero] at hvb
  linear_combination hvb - hv

/-- Coefficients on two distinct nontrivial coordinate axes multiply to zero. -/
theorem axis_product_zero [DecidableEq M] (Φ : V →ₗ[ℂ] Array κ)
    (h : ∀ v, MinorsVanish (Φ v)) (v₀ : V) (p : (e : M) → κ e)
    (hbase : Φ v₀ = delta p) (v : V) (e f : M) (hef : e ≠ f)
    (a : κ e) (b : κ f) (ha : a ≠ p e) (hb : b ≠ p f) :
    Φ v (update p e a) * Φ v (update p f b) = 0 := by
  classical
  have hm := h v e (update p e a) (update p f b)
  have hdouble : Φ v (update (update p f b) e a) = 0 := by
    apply two_changes_zero Φ h v₀ p hbase v _ e f hef
    · simpa using ha
    · simpa [update_of_ne (Ne.symm hef)] using hb
  simpa only [update_of_ne hef, update_self, update_idem, update_eq_self,
    hdouble, mul_zero, sub_zero] using hm

/-- The image of a linear family through a coordinate basis tensor has support
on a single coordinate axis, with that axis derived from the minor equations. -/
theorem exists_axis_support [DecidableEq M] [Nonempty M] (Φ : V →ₗ[ℂ] Array κ)
    (h : ∀ v, MinorsVanish (Φ v)) (v₀ : V) (p : (e : M) → κ e)
    (hbase : Φ v₀ = delta p) :
    ∃ e : M, ∀ (v : V) (x : (e : M) → κ e) (f : M),
      f ≠ e → x f ≠ p f → Φ v x = 0 := by
  classical
  by_cases hex : ∃ (e : M) (a : κ e) (v : V), a ≠ p e ∧ Φ v (update p e a) ≠ 0
  · obtain ⟨e, a, v, ha, hva⟩ := hex
    refine ⟨e, ?_⟩
    intro w x f hfe hxf
    by_cases hother : ∃ g, g ≠ f ∧ x g ≠ p g
    · obtain ⟨g, hgf, hxg⟩ := hother
      exact two_changes_zero Φ h v₀ p hbase w x f g (Ne.symm hgf) hxf hxg
    · have hxeq : x = update p f (x f) := by
        funext g
        by_cases hgf : g = f
        · subst g; simp
        · rw [update_of_ne hgf]
          by_contra hneq
          exact hother ⟨g, hgf, hneq⟩
      rw [hxeq]
      let L : V →ₗ[ℂ] ℂ := (LinearMap.proj (update p e a)).comp Φ
      let R : V →ₗ[ℂ] ℂ := (LinearMap.proj (update p f (x f))).comp Φ
      have hprod : ∀ z, L z * R z = 0 := fun z =>
        axis_product_zero Φ h v₀ p hbase z e f (Ne.symm hfe) a (x f) ha hxf
      have hr : R v = 0 := (mul_eq_zero.mp (hprod v)).resolve_left hva
      have hcross := cross_zero_of_pointwise_product L R hprod v w
      rw [hr, mul_zero, add_zero] at hcross
      exact (mul_eq_zero.mp hcross).resolve_left hva
  · obtain ⟨e⟩ := ‹Nonempty M›
    refine ⟨e, ?_⟩
    intro v x f _ hxf
    by_cases hother : ∃ g, g ≠ f ∧ x g ≠ p g
    · obtain ⟨g, hgf, hxg⟩ := hother
      exact two_changes_zero Φ h v₀ p hbase v x f g (Ne.symm hgf) hxf hxg
    · have hxeq : x = update p f (x f) := by
        funext g
        by_cases hgf : g = f
        · subst g; simp
        · rw [update_of_ne hgf]
          by_contra hneq
          exact hother ⟨g, hgf, hneq⟩
      rw [hxeq]
      by_contra hn
      exact hex ⟨f, x f, v, hxf, hn⟩

/-- Coordinate slices remain linear in the original parameter. -/
def axisSlice [DecidableEq M] (Φ : V →ₗ[ℂ] Array κ) (p : (e : M) → κ e)
    (e : M) : V →ₗ[ℂ] (κ e → ℂ) where
  toFun v a := Φ v (update p e a)
  map_add' v w := by ext a; simp
  map_smul' c v := by ext a; simp

/-- Standard fixed factor coordinates. -/
def deltaFactors (p : (e : M) → κ e) : (e : M) → κ e → ℂ := by
  classical
  exact fun e a => if a = p e then 1 else 0

theorem product_factor_update [DecidableEq M] (U : (e : M) → κ e → ℂ)
    (e : M) (z : κ e → ℂ) (x : (e : M) → κ e) :
    product (update U e z) x = z (x e) * ∏ f ∈ Finset.univ.erase e, U f (x f) := by
  unfold product
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ e)]
  simp only [update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro f hf
  rw [update_of_ne (Finset.ne_of_mem_erase hf)]

/-- A supported coordinate array is precisely its one-factor reconstruction. -/
theorem eq_product_of_axis_support [DecidableEq M] (A : Array κ)
    (p : (e : M) → κ e) (e : M)
    (hs : ∀ (x : (e : M) → κ e) (f : M), f ≠ e → x f ≠ p f → A x = 0) :
    A = product (update (deltaFactors p) e (fun a => A (update p e a))) := by
  classical
  funext x
  rw [product_factor_update]
  by_cases hx : ∀ f, f ≠ e → x f = p f
  · have hx' : x = update p e (x e) := by
      funext f
      by_cases hfe : f = e
      · subst f; simp
      · rw [update_of_ne hfe]; exact hx f hfe
    have hp : (∏ f ∈ Finset.univ.erase e, deltaFactors p f (x f)) = 1 := by
      apply Finset.prod_eq_one
      intro f hf
      simp [deltaFactors, hx f (Finset.ne_of_mem_erase hf)]
    rw [hp, mul_one, ← hx']
  · push Not at hx
    obtain ⟨f, hfe, hxf⟩ := hx
    rw [hs x f hfe hxf]
    have hp : (∏ g ∈ Finset.univ.erase e, deltaFactors p g (x g)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hfe, Finset.mem_univ f⟩)
      simp [deltaFactors, hxf]
    rw [hp, mul_zero]

/-- A linear coordinate family through a basis tensor lies in a derived ruling. -/
theorem coordinate_linear_ruling [DecidableEq M] [Nonempty M]
    (Φ : V →ₗ[ℂ] Array κ) (h : ∀ v, MinorsVanish (Φ v))
    (v₀ : V) (p : (e : M) → κ e) (hbase : Φ v₀ = delta p) :
    ∃ e : M, ∀ v, Φ v = product (update (deltaFactors p) e (axisSlice Φ p e v)) := by
  obtain ⟨e, he⟩ := exists_axis_support Φ h v₀ p hbase
  exact ⟨e, fun v => eq_product_of_axis_support (Φ v) p e (he v)⟩

end Holant.Platonic.FixedMatchingRuling.Segre
