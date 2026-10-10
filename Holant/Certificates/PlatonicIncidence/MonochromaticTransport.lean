import Holant.Certificates.PlatonicIncidence.MonochromaticRainbow
import Holant.Certificates.RainbowOrbit.GeneratedOrbit
import Holant.Certificates.RainbowOrbit.ExternalDeckIntegration

/-! Analytic transport of monochromatic incidence. These linear similarities
are coefficient dictionaries, never assertions of realizability by gadgets. -/
namespace Holant.Certificates.PlatonicIncidence
open Holant Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
open Holant.Certificates.OctahedralSeparator
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem linearEquiv_proportional_iff (E : BinaryMatrix ≃ₗ[ℂ] BinaryMatrix) (U V : BinaryMatrix) :
    Proportional (E U) (E V) ↔ Proportional U V := by
  constructor
  · rintro ⟨c,hc,he⟩
    refine ⟨c,hc,E.injective ?_⟩
    simpa only [map_smul] using he
  · rintro ⟨c,hc,rfl⟩
    exact ⟨c,hc,map_smul E c V⟩

theorem linearEquiv_mem_span_pair_iff (E : BinaryMatrix ≃ₗ[ℂ] BinaryMatrix)
    (U V W : BinaryMatrix) :
    E W∈Submodule.span ℂ ({E U,E V} : Set BinaryMatrix) ↔
      W∈Submodule.span ℂ ({U,V} : Set BinaryMatrix) := by
  constructor
  · intro h
    obtain ⟨a,b,he⟩ := Submodule.mem_span_pair.mp h
    exact Submodule.mem_span_pair.mpr ⟨a,b,E.injective (by simpa only [map_add,map_smul] using he)⟩
  · intro h
    obtain ⟨a,b,he⟩ := Submodule.mem_span_pair.mp h
    exact Submodule.mem_span_pair.mpr ⟨a,b,by simpa only [map_add,map_smul] using congrArg E he⟩

/-- Domain secants, including their full finite intersections, are preserved
by any invertible complex coefficient operator. -/
theorem binarySecant_linearEquiv_iff (E : BinaryMatrix ≃ₗ[ℂ] BinaryMatrix)
    (K : ι → BinaryMatrix) (L : Finset ι) :
    BinarySecant (fun i => E (K i)) L ↔ BinarySecant K L := by
  constructor <;> rintro ⟨i,j,hij,hL⟩ <;> refine ⟨i,j,hij,?_⟩ <;> intro k
  · exact (hL k).trans (linearEquiv_mem_span_pair_iff E _ _ _)
  · exact (hL k).trans (linearEquiv_mem_span_pair_iff E _ _ _).symm

/-- Literal conjugation operator used by the marked and external dictionaries. -/
def thetaLinearEquiv (f : Form) : BinaryMatrix ≃ₗ[ℂ] BinaryMatrix where
  toFun := complexTheta f
  invFun := complexPull f
  left_inv := complexPull_complexTheta f
  right_inv := complexTheta_complexPull f
  map_add' U V := by simp [complexTheta,Matrix.mul_add,Matrix.add_mul]
  map_smul' c U := complexTheta_smul f c U

theorem external_binarySecant_iff (L : Finset (Fin 12)) :
    BinarySecant External.representative L ↔ BinarySecant (representative .tetrahedral) L := by
  have he : External.representative=(fun i => thetaLinearEquiv 2 (representative .tetrahedral i)) := by
    funext i
    exact External.representative_eq_theta i
  rw [he]
  exact binarySecant_linearEquiv_iff _ _ _

theorem external_representative_faithful (i j : Fin 12)
    (h : Proportional (External.representative i) (External.representative j)) : i=j := by
  obtain ⟨c,_,hc⟩ := h
  exact External.projectively_injective i j c hc

theorem markedRepresentative_eq_theta (f : Form) (i : Fin 24) :
    markedRepresentative f i=thetaLinearEquiv f (representative .octahedral i) := by
  rw [markedRepresentative,complexMatrix_theta,←octahedralRaw_standard]
  rfl

theorem marked_binarySecant_iff (f : Form) (L : Finset (Fin 24)) :
    BinarySecant (markedRepresentative f) L ↔ BinarySecant (representative .octahedral) L := by
  have he : markedRepresentative f=(fun i => thetaLinearEquiv f (representative .octahedral i)) := by
    funext i
    exact markedRepresentative_eq_theta f i
  rw [he]
  exact binarySecant_linearEquiv_iff _ _ _

theorem marked_representative_faithful (f : Form) (i j : Fin 24)
    (h : Proportional (markedRepresentative f i) (markedRepresentative f j)) : i=j := by
  rw [markedRepresentative_eq_theta,markedRepresentative_eq_theta] at h
  obtain ⟨c,_,hc⟩ := (linearEquiv_proportional_iff (thetaLinearEquiv f) _ _).mp h
  exact projectively_injective .octahedral i j c hc

/-- The finite representatives enumerate exactly the semantic projective deck,
including arbitrary nonzero scales on both ordered factors. -/
theorem configurationDeck_iff_familyDeckPoint (K : ι → BinaryMatrix)
    (hdet : ∀i,(K i).det≠0) (G : BinaryMatrix→Prop) (hG : ∀i,G (K i))
    (hcomplete : ∀U,G U→∃i,Proportional U (K i)) (q : Point) :
    q∈configurationPoints K hdet Finset.univ ↔ FamilyDeckPoint G q := by
  classical
  constructor
  · intro h
    obtain ⟨⟨r,i,j⟩,_,rfl⟩ := Finset.mem_image.mp h
    exact ⟨r,_,_,⟨K i,K j,hG i,hG j,rfl⟩,rfl⟩
  · rintro ⟨r,F,hF,⟨U,V,hU,hV,rfl⟩,rfl⟩
    obtain ⟨i,hi⟩ := hcomplete U hU
    obtain ⟨j,hj⟩ := hcomplete V hV
    have he := (proportional_point_iff _ _ hF (configurationTensor_nonzero K hdet (r,i,j))).mp
      (matching_proportional r hi hj)
    exact Finset.mem_image.mpr ⟨(r,i,j),Finset.mem_univ _,he.symm⟩

end
end Holant.Certificates.PlatonicIncidence
