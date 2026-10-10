import Holant.Certificates.TetrahedralBridge.Basis
import Holant.Certificates.TetrahedralBridge.Triples

/-! Exhaustivity and distinctness for actual complex-linear coefficient maps,
not just a list of indexed tuples. Every map is an actual Frobenius card map. -/
namespace Holant.Certificates.TetrahedralBridge
open Holant Holant.Certificates.MatchingProductBridge
noncomputable section

def sourceImages (i : Fin 12) : Fin 4 → FourTensor :=
  ![(1/2 : ℂ) • C,orderedTuple i 0,orderedTuple i 1,orderedTuple i 2]
def sourceMap (i : Fin 12) : Binary →ₗ[ℂ] FourTensor := mapFromImages (sourceImages i)

theorem sourceMap_basis (i : Fin 12) (k : Fin 4) : sourceMap i (quaternionBasis k) = sourceImages i k :=
  mapFromImages_basis _ _

theorem sourceMap_next (i : Fin 12) (j : Fin 3) :
    sourceMap i (quaternionBasis j.succ) = orderedTuple i j := by
  rw [sourceMap_basis]
  fin_cases j <;> rfl

/-- This identifies every displayed coefficient map with the existing actual
bilinear contraction of its six-port tensor. -/
theorem sourceMap_contract (i : Fin 12) (U : Binary) :
    sourceMap i U = Signature.contract U (reconstruct (sourceImages i)) :=
  mapFromImages_eq_contract _ _

/-- Exactly the source's normalization and separated-sign sum constraints. -/
def Normalized (Φ : Binary →ₗ[ℂ] FourTensor) : Prop :=
  Φ (quaternionBasis 0) = (1/2 : ℂ) • C ∧
    (∀ j : Fin 3, bridgeConditions .tetrahedral (Φ (quaternionBasis j.succ))) ∧
    Φ (quaternionBasis 1)+Φ (quaternionBasis 2)+Φ (quaternionBasis 3)=target

/-- No finite-candidate coverage is assumed for Φ. It is recovered from its four
actual basis images after full cone completeness and the checked sum equation. -/
theorem normalized_iff (Φ : Binary →ₗ[ℂ] FourTensor) :
    Normalized Φ ↔ ∃ i : Fin 12, Φ = sourceMap i := by
  constructor
  · rintro ⟨h0,hG,hS⟩
    let W : Fin 3 → FourTensor := fun j => Φ (quaternionBasis j.succ)
    obtain ⟨i,hi⟩ := (triple_iff W).mp ⟨hG,hS⟩
    refine ⟨i,map_ext_basis ?_⟩
    intro k
    rw [sourceMap_basis]
    fin_cases k
    · exact h0
    · exact congrFun hi 0
    · exact congrFun hi 1
    · exact congrFun hi 2
  · rintro ⟨i,rfl⟩
    have h := (triple_iff (orderedTuple i)).mpr ⟨i,rfl⟩
    refine ⟨sourceMap_basis i 0,?_,?_⟩
    · intro j
      rw [sourceMap_next]
      exact h.1 j
    · change sourceMap i (quaternionBasis (0 : Fin 3).succ)+
        sourceMap i (quaternionBasis (1 : Fin 3).succ)+sourceMap i (quaternionBasis (2 : Fin 3).succ)=target
      simp only [sourceMap_next]
      exact h.2

theorem sourceMap_injective : Function.Injective sourceMap := by
  intro i j h
  apply orderedTuple_injective
  funext k
  have he := congrArg (fun Φ : Binary →ₗ[ℂ] FourTensor => Φ (quaternionBasis k.succ)) h
  simpa only [sourceMap_next] using he

noncomputable def normalizedMaps : Finset (Binary →ₗ[ℂ] FourTensor) := by
  classical
  exact Finset.univ.image sourceMap

theorem normalizedMaps_card : normalizedMaps.card = 12 := by
  classical
  rw [normalizedMaps,Finset.card_image_of_injective _ sourceMap_injective]
  simp

theorem mem_normalizedMaps (Φ : Binary →ₗ[ℂ] FourTensor) : Φ ∈ normalizedMaps ↔ Normalized Φ := by
  classical
  rw [normalized_iff]
  simp [normalizedMaps,eq_comm]

end
end Holant.Certificates.TetrahedralBridge
