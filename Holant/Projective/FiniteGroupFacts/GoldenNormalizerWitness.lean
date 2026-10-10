import Holant.Projective.FiniteGroupFacts.ModelInclusions

/-! One actual octahedral element fails to normalize the actual icosahedral
model. The separating integer calculations have proved complex-matrix semantics. -/
namespace Holant.Projective.FiniteGroupFacts
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
open Holant.Projective.BoundedTorsion
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option synthInstance.maxSize 100000

def rejectedGoldenConjugate : GoldenVector :=
  goldenQuaternionProduct (goldenQuaternionProduct (octahedralRaw 12) (icosahedralRaw 12))
    (octahedralRaw 13)

theorem rejectedGoldenConjugate_separation : ∀ k : Fin 60,
    ∃ a b : Fin 4, GoldenInt.norm (goldenCross rejectedGoldenConjugate (icosahedralRaw k) a b) ≠ 0 := by
  decide +kernel

theorem rejectedGoldenConjugate_not_direction :
    ¬ groupDirection .icosahedral (goldenMatrix rejectedGoldenConjugate) := by
  intro h
  obtain ⟨k, c, hc, he⟩ := (complete .icosahedral _).mp h
  obtain ⟨a, b, hn⟩ := rejectedGoldenConjugate_separation k
  exact GoldenInt.eval_ne_zero _ hn
    (goldenCross_projective_zero rejectedGoldenConjugate (icosahedralRaw k) c he a b)

theorem octahedral_twelve_inverse :
    (indexedPGL .octahedral (12 : Fin 24))⁻¹ = indexedPGL .octahedral (13 : Fin 24) := by
  apply inv_eq_of_mul_eq_one_right
  rw [indexedPGL_product]
  change indexedPGL .octahedral (0 : Fin 24) = 1
  exact indexedPGL_identity .octahedral

theorem octahedral_twelve_not_normalizer_icosahedral :
    (indexedPGL .octahedral (12 : Fin 24) : PGL2 ℂ) ∉
      Subgroup.normalizer (modelPGL .icosahedral : Set (PGL2 ℂ)) := by
  intro hn
  have hm := (hn (indexedPGL .icosahedral (12 : Fin 60) : PGL2 ℂ)).mp
    (indexedPGL .icosahedral (12 : Fin 60)).property
  have hinv : (indexedPGL .octahedral (12 : Fin 24) : PGL2 ℂ)⁻¹ =
      (indexedPGL .octahedral (13 : Fin 24) : PGL2 ℂ) := congrArg Subtype.val octahedral_twelve_inverse
  rw [hinv] at hm
  change pglMk ℂ (representativeGL .octahedral (12 : Fin 24)) *
    pglMk ℂ (representativeGL .icosahedral (12 : Fin 60)) * pglMk ℂ (representativeGL .octahedral (13 : Fin 24)) ∈ _ at hm
  rw [← map_mul, ← map_mul] at hm
  have hmdir := (pglMk_mem_model_iff .icosahedral
    (representativeGL .octahedral (12 : Fin 24) *
      representativeGL .icosahedral (12 : Fin 60) *
      representativeGL .octahedral (13 : Fin 24))).mp hm
  apply rejectedGoldenConjugate_not_direction
  change groupDirection .icosahedral
    (representative .octahedral (12 : Fin 24) * representative .icosahedral (12 : Fin 60) *
      representative .octahedral (13 : Fin 24)) at hmdir
  simpa only [representative, raw, rejectedGoldenConjugate, goldenMatrix_product] using hmdir

end
end Holant.Projective.FiniteGroupFacts
