import Holant.Projective.CyclicPhasePencil.Basic

/-! Cyclic phase-pencil rigidity with all degenerate endpoint and sample cases.
The complex statement is proved directly from root-polygon interpolation; no
assumption of sample nonvanishing, generic position, or endpoint rank is added. -/
noncomputable section
namespace Holant.Projective.CyclicPhasePencil

/-- Vanishing at the actual root polygon forces both affine coefficients zero. -/
theorem affine_zero {m : ℕ} (hm : 3≤m) (a b : ℂ)
    (h : ∀ s : ℂ, s^m=1 → a-s*b=0) : a=0 ∧ b=0 := by
  have hh := affine_product_zero_on_rootPolygon hm a (-b) 1 0 (by
    intro s hs
    simpa [sub_eq_add_neg] using h s hs)
  rcases hh with hab | hf
  · exact ⟨hab.1,neg_eq_zero.mp hab.2⟩
  · exact (one_ne_zero hf.1).elim

/-- A zero denominator at every root is exactly the all-zero pencil case. -/
theorem all_zero_of_denominator_zero {m : ℕ} (hm : 3≤m) (a b c d : ℂ)
    (hs : ScalarSamples m a b c d)
    (hz : ∀ s : ℂ, s^m=1 → a-s*b=0) : a=0 ∧ b=0 ∧ c=0 ∧ d=0 := by
  obtain ⟨ha,hb⟩ := affine_zero hm a b hz
  have hnum : ∀ s : ℂ, s^m=1 → c-s*d=0 := by
    intro s hr
    rcases hs s hr with hzero | hnonzero
    · linear_combination -hzero.2
    · exact (hnonzero.1 (hz s hr)).elim
  obtain ⟨hc,hd⟩ := affine_zero hm c d hnum
  exact ⟨ha,hb,hc,hd⟩

/-- The dependent affine forms acquire a genuine root multiplier from one
nonzero sample. That sample exists unless every endpoint is zero. -/
theorem relation_of_det_zero {m : ℕ} (hm : 3≤m) (a b c d : ℂ)
    (hs : ScalarSamples m a b c d) (hdet : a*d-b*c=0) : Relation m a b c d := by
  by_cases hz : ∀ s : ℂ, s^m=1 → a-s*b=0
  · obtain ⟨rfl,rfl,rfl,rfl⟩ := all_zero_of_denominator_zero hm a b c d hs hz
    exact relation_zero m
  push_neg at hz
  obtain ⟨s,hr,hv⟩ := hz
  have hphase : ((-c+s*d)/(a-s*b))^m=1 := by
    rcases hs s hr with hzero | hnonzero
    · exact (hv hzero.1).elim
    · exact hnonzero.2.2
  let α := (-c+s*d)/(a-s*b)
  have heq : α*(a-s*b)= -c+s*d := div_mul_cancel₀ _ hv
  have hcprod : (α*a+c)*(a-s*b)=0 := by
    calc
      (α*a+c)*(a-s*b)=a*(α*(a-s*b))+c*(a-s*b) := by ring
      _ = s*(a*d-b*c) := by rw [heq]; ring
      _ = 0 := by rw [hdet,mul_zero]
  have hdprod : (α*b+d)*(a-s*b)=0 := by
    calc
      (α*b+d)*(a-s*b)=b*(α*(a-s*b))+d*(a-s*b) := by ring
      _ = a*d-b*c := by rw [heq]; ring
      _ = 0 := hdet
  have hc := (mul_eq_zero.mp hcprod).resolve_right hv
  have hd := (mul_eq_zero.mp hdprod).resolve_right hv
  refine ⟨α,hphase,Or.inl ⟨?_,?_⟩⟩
  · linear_combination hc
  · linear_combination hd

/-- Forward implication in the exact source relation, including both singular
and independent pencils. -/
theorem relation_of_samples {m : ℕ} (hm : 3≤m) (a b c d : ℂ)
    (hs : ScalarSamples m a b c d) : Relation m a b c d := by
  by_cases hdet : a*d-b*c=0
  · exact relation_of_det_zero hm a b c d hs hdet
  have hpole (s : ℂ) (hr : s^m=1) : a+(-b)*s≠0 := by
    intro hz
    have hz' : a-s*b=0 := by linear_combination hz
    have hu : -c+s*d=0 := by
      rcases hs s hr with hzero | hnonzero
      · exact hzero.2
      · exact (hnonzero.1 hz').elim
    apply hdet
    linear_combination d*hz'+b*hu
  have hroots : Set.MapsTo (fun s : ℂ => (-c+d*s)/(a+(-b)*s)) (rootPolygon m) (rootPolygon m) := by
    intro s hr
    rcases hs s hr with hzero | hnonzero
    · exact (hpole s hr (by linear_combination hzero.1)).elim
    · simpa [rootPolygon,sub_eq_add_neg,mul_comm] using hnonzero.2.2
  have hdet' : a*d-(-b)*(-c)≠0 := by simpa using hdet
  obtain ⟨α,hα,h | h⟩ := root_polygon_coefficients hm a (-b) (-c) d hdet' hpole hroots
  · obtain ⟨hb,hc,ha,hd⟩ := h
    exact ⟨α,hα,Or.inr (Or.inl ⟨neg_eq_zero.mp hb,neg_eq_zero.mp hc,hd⟩)⟩
  · obtain ⟨ha,hd,hb,hc⟩ := h
    refine ⟨α,hα,Or.inr (Or.inr ⟨ha,hd,?_⟩)⟩
    linear_combination -hc

section Converse
variable {K : Type*} [Field K]

theorem scalarSample_of_root {m : ℕ} (hm : 0<m) {α : K} (hα : α^m=1) (v : K) :
    ScalarSample m v (α*v) := by
  by_cases hv : v=0
  · exact Or.inl ⟨hv,by simp [hv]⟩
  · exact Or.inr ⟨hv,mul_ne_zero (root_ne_zero hm hα) hv,by simpa [hv] using hα⟩

/-- Every source alternative gives every physical phase sample; zero endpoint
and cancellation cases are retained without imposing nonsingularity. -/
theorem samples_of_relation {m : ℕ} (hm : 0<m) (a b c d : K)
    (h : Relation m a b c d) : ScalarSamples m a b c d := by
  obtain ⟨α,hα,h | h | h⟩ := h
  · obtain ⟨hc,hd⟩ := h
    intro s hs
    have he : -c+s*d=α*(a-s*b) := by rw [hc,hd]; ring
    rw [he]
    exact scalarSample_of_root hm hα _
  · obtain ⟨hb,hc,hd⟩ := h
    intro s hs
    have he : -c+s*d=(s*α)*(a-s*b) := by rw [hb,hc,hd]; ring
    rw [he]
    apply scalarSample_of_root hm
    rw [mul_pow,hs,hα,mul_one]
  · obtain ⟨ha,hd,hc⟩ := h
    intro s hs
    have hs0 := root_ne_zero hm hs
    have he : -c+s*d=(α/s)*(a-s*b) := by rw [ha,hd,hc]; field_simp; ring
    rw [he]
    apply scalarSample_of_root hm
    rw [div_pow,hα,hs,div_one]
end Converse

/-- Full complex scalar form of manuscript Lemma 7.1. -/
theorem relation_iff_scalarSamples {m : ℕ} (hm : 3≤m) (a b c d : ℂ) :
    Relation m a b c d ↔ ScalarSamples m a b c d :=
  ⟨samples_of_relation (by omega) a b c d,relation_of_samples hm a b c d⟩

/-- Manuscript Lemma 7.1 (`lem:odd-dih-RN`), over the larger complex coefficient
field: the literal transfer matrix diag(a-sb,c-sd)Z is zero or projectively D_eta
at every actual m-th root exactly when one of the three stated systems holds. -/
theorem cyclic_phase_pencil {m : ℕ} (hm : 3≤m) (a b c d : ℂ) :
    Relation m a b c d ↔ MatrixSamples m a b c d := by
  rw [matrixSamples_iff (by omega),relation_iff_scalarSamples hm]

end Holant.Projective.CyclicPhasePencil
