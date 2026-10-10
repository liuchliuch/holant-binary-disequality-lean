import Holant.Certificates.PlatonicIncidence.MonochromaticRuling
import Holant.Platonic.RainbowLocalization.ProductFactorProjectivity

/-! Three tensors on a rank-one split line share their complementary factor
when their first factors are not projectively equal. All scales are recorded. -/
namespace Holant.Platonic.RainbowLocalization
noncomputable section
open Holant.Certificates.RainbowOrbit Holant.Certificates.PlatonicIncidence
variable {S T : Type*} [Fintype S] [Fintype T]

 theorem outer_equal_right_proportional (u w : S→ℂ) (v r : T→ℂ)
    (hu : u≠0) (hv : v≠0)
    (h : Matrix.vecMulVec u v=Matrix.vecMulVec w r) : Proportional v r := by
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hu
  obtain ⟨j,hj⟩ := Function.ne_iff.mp hv
  have hi0 : u i≠0 := hi
  have he (k : T) : u i*v k=w i*r k := congrArg (fun A : Matrix S T ℂ=>A i k) h
  have hw : w i≠0 := by
    intro hz
    have hh := he j
    rw [hz,zero_mul] at hh
    exact (mul_ne_zero hi hj) hh
  refine ⟨w i/u i,div_ne_zero hw hi,?_⟩
  funext k
  change v k=(w i/u i)*r k
  apply (mul_left_cancel₀ hi)
  calc
    u i*v k=w i*r k := he k
    _=u i*((w i/u i)*r k) := by field_simp [hi0]

/-- The complement is the actual second tensor's complementary factor; its
nonzero scales on the other two tensors are conclusions of the line equation. -/
 theorem three_split_tensors_common_complement
    (u₀ u₁ u₂ : S→ℂ) (v₀ v₁ v₂ : T→ℂ)
    (hu₀ : u₀≠0) (hu₁ : u₁≠0) (hu₂ : u₂≠0)
    (hv₀ : v₀≠0) (hv₁ : v₁≠0) (hv₂ : v₂≠0)
    (hsep : ¬Proportional u₀ u₁) (a b : ℂ) (ha : a≠0) (hb : b≠0)
    (hline : Matrix.vecMulVec u₂ v₂=
      a • Matrix.vecMulVec u₀ v₀+b • Matrix.vecMulVec u₁ v₁) :
    ∃s₀ s₂ : ℂ,s₀≠0 ∧ s₂≠0 ∧ v₀=s₀ • v₁ ∧ v₂=s₂ • v₁ ∧
      s₂ • u₂=a • (s₀ • u₀)+b • u₁ := by
  have hrank : (a • Matrix.vecMulVec u₀ v₀+b • Matrix.vecMulVec u₁ v₁).rank≤1 := by
    rw [←hline]
    exact Matrix.rank_vecMulVec_le _ _
  have hp := outer_sum_rank_le_one_ruling u₀ u₁ v₀ v₁
    (Function.ne_iff.mp hu₀) (Function.ne_iff.mp hu₁)
    (Function.ne_iff.mp hv₀) (Function.ne_iff.mp hv₁) a b ha hb hrank
  obtain ⟨s₀,hs₀,hv₀'⟩ := hp.resolve_left hsep
  have he : Matrix.vecMulVec u₂ v₂=Matrix.vecMulVec (a • (s₀ • u₀)+b • u₁) v₁ := by
    rw [hline,hv₀']
    ext i j
    simp only [Matrix.add_apply,Matrix.smul_apply,Matrix.vecMulVec_apply,
      Pi.smul_apply,Pi.add_apply,smul_eq_mul]
    ring
  obtain ⟨s₂,hs₂,hv₂'⟩ := outer_equal_right_proportional u₂ _ v₂ v₁ hu₂ hv₂ he
  refine ⟨s₀,s₂,hs₀,hs₂,hv₀',hv₂',?_⟩
  obtain ⟨j,hj⟩ := Function.ne_iff.mp hv₁
  funext i
  have hh := congrArg (fun A : Matrix S T ℂ=>A i j) he
  rw [hv₂'] at hh
  simp only [Matrix.vecMulVec_apply,Pi.smul_apply,Pi.add_apply,smul_eq_mul] at hh ⊢
  apply (mul_right_cancel₀ hj)
  calc
    (s₂*u₂ i)*v₁ j=u₂ i*(s₂*v₁ j) := by ring
    _=(a*(s₀*u₀ i)+b*u₁ i)*v₁ j := hh

end
end Holant.Platonic.RainbowLocalization
