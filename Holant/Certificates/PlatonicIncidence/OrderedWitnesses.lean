import Holant.Certificates.PlatonicIncidence.OppositeTransitivity

/-! Ordered-port witnesses required by A.20(ii). The identity permutation is
recorded explicitly; the actual four-boundary native-X network remains the
same network already proved for the source representatives. -/
namespace Holant.Certificates.PlatonicIncidence
open Holant Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
open Holant.Certificates.OctahedralSeparator
noncomputable section
set_option backward.isDefEq.respectTransparency false

def OrderedPhysicalWitness {n : ℕ} (K : Fin n→BinaryMatrix) (F H : Fin 3→FourTensor) : Prop :=
  ∃σ : Equiv.Perm (Fin 4),σ=Equiv.refl (Fin 4) ∧
    ∃k : Fin 4→Fin n,∃lam : Fin 3→ℂ,(∀r,lam r≠0) ∧
      ∀r,(physicalNetwork (Tensor.reindex σ (F r)) (fun j => K (k j))).denote=lam r • H r

theorem orderedWitness_of_word {n : ℕ} (K : Fin n→BinaryMatrix) (F H : Fin 3→FourTensor)
    (h : ∃k : Fin 4→Fin n,∃lam : Fin 3→ℂ,(∀r,lam r≠0) ∧
      ∀r,(physicalNetwork (F r) (fun j => K (k j))).denote=lam r • H r) :
    OrderedPhysicalWitness K F H := by
  obtain ⟨k,lam,hlam,he⟩ := h
  refine ⟨Equiv.refl _,rfl,k,lam,hlam,?_⟩
  intro r
  rw [Tensor.reindex_refl]
  exact he r

theorem ordered_standard_normalization (g : PlatonicModel) (p : Fin 3→Point) (hp : Rainbow g p) :
    OrderedPhysicalWitness (representative g) (fun r => (p r).rep) base :=
  orderedWitness_of_word _ _ _ (actual_standard_normalization g p hp)

theorem ordered_marked_normalization (f : Form) (p : Fin 3→Point) (hp : MarkedRainbow f p) :
    OrderedPhysicalWitness (markedRepresentative f) (fun r => (p r).rep) (markedInitial f) :=
  orderedWitness_of_word _ _ _ (actual_marked_normalization f p hp)

theorem ordered_opposite_transitivity (p q : Fin 3→Point)
    (hp : Opposite.Rainbow p) (hq : Opposite.Rainbow q) :
    OrderedPhysicalWitness OppositeIcosahedral.oppositeRepresentative
      (fun r => (p r).rep) (fun r => (q r).rep) :=
  orderedWitness_of_word _ _ _ (Opposite.actual_transitivity p q hp hq)

end
end Holant.Certificates.PlatonicIncidence
