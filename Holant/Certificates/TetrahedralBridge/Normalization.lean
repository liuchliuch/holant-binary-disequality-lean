import Holant.Certificates.TetrahedralBridge.Maps

/-! Exact equivalence with the manuscript's two displayed normalization inputs,
Q0+Q1+Q2+Q3 and Q0-Q1-Q2-Q3. No image equation is silently strengthened. -/
namespace Holant.Certificates.TetrahedralBridge
open Holant Holant.Certificates.MatchingProductBridge
noncomputable section

def normalPlus : Binary := Q0+Q1+Q2+Q3
def normalMinus : Binary := Q0-Q1-Q2-Q3

theorem normalization_iff (Φ : Binary →ₗ[ℂ] FourTensor) :
    (Φ normalPlus = A ∧ Φ normalMinus = -B) ↔
      (Φ Q0 = (1/2 : ℂ) • C ∧ Φ Q1+Φ Q2+Φ Q3=target) := by
  constructor
  · rintro ⟨hp,hm⟩
    constructor
    · funext x
      have hpx := congrFun hp x
      have hmx := congrFun hm x
      have hc := congrFun A_sub_B x
      simp only [normalPlus,normalMinus,map_add,map_sub,Pi.add_apply,Pi.sub_apply,Pi.neg_apply] at hpx hmx hc
      change Φ Q0 x = (1/2 : ℂ)*C x
      linear_combination hpx/2+hmx/2+hc/2
    · funext x
      have hpx := congrFun hp x
      have hmx := congrFun hm x
      simp only [normalPlus,normalMinus,map_add,map_sub,Pi.add_apply,Pi.sub_apply,Pi.neg_apply] at hpx hmx
      change Φ Q1 x+Φ Q2 x+Φ Q3 x=(A x+B x)/2
      linear_combination hpx/2-hmx/2
  · rintro ⟨h0,hS⟩
    constructor
    · funext x
      have hz := congrFun h0 x
      have hs := congrFun hS x
      have hc := congrFun A_sub_B x
      simp only [Pi.smul_apply,smul_eq_mul,Pi.add_apply,Pi.sub_apply,target] at hz hs hc
      simp only [normalPlus,map_add,Pi.add_apply]
      linear_combination hz+hs-hc/2
    · funext x
      have hz := congrFun h0 x
      have hs := congrFun hS x
      have hc := congrFun A_sub_B x
      simp only [Pi.smul_apply,smul_eq_mul,Pi.add_apply,Pi.sub_apply,target] at hz hs hc
      simp only [normalMinus,map_sub,Pi.sub_apply,Pi.neg_apply]
      linear_combination hz-hs-hc/2

theorem normalized_iff_source (Φ : Binary →ₗ[ℂ] FourTensor) :
    Normalized Φ ↔ (Φ normalPlus = A ∧ Φ normalMinus = -B) ∧
      ∀ j : Fin 3, bridgeConditions .tetrahedral (Φ (quaternionBasis j.succ)) := by
  constructor
  · rintro ⟨h0,hG,hS⟩
    exact ⟨(normalization_iff Φ).mpr ⟨h0,hS⟩,hG⟩
  · rintro ⟨hN,hG⟩
    obtain ⟨h0,hS⟩ := (normalization_iff Φ).mp hN
    exact ⟨h0,hG,hS⟩

end
end Holant.Certificates.TetrahedralBridge
