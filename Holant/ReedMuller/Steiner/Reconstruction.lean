import Holant.ReedMuller.Steiner.Embedding

namespace Holant.ReedMuller.Steiner
open Holant.ReedMuller.LowArity Holant.ReedMuller.CoefficientAtlas
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

/-- A ninth coordinate would give a weight-four block with between two and
three coordinates in the embedded RM code, contradicting its minimum weight. -/
theorem Configuration.surjective {D : BinaryCode n} (C : Configuration D)
    (hD : SelfDual D) (hS : SteinerProperty D) : Function.Surjective C.points := by
  intro z
  by_contra hz
  have hout : ∀ k,C.points k≠z := by simpa using hz
  have h01 : C.points 0≠C.points 1 := C.points.injective.ne (by decide)
  obtain ⟨B,hB,_⟩ := hS (C.points 0) (C.points 1) z h01 (hout 0) (hout 1)
  obtain ⟨a,ha⟩ := C.restriction hD (indicator B) hB.1.2
  have hane : prototype a≠0 := by
    intro he
    have H := congrFun ha 0
    rw [he] at H
    simpa [indicator,hB.2.1] using H
  have hlow := prototype_min_weight a hane
  let S : Finset (Fin 8) := Finset.univ.filter fun k => C.points k∈B
  have hs : support (prototype a)=S := by
    rw [ha]
    ext k
    simp [support,indicator,S]
  have himage : S.image C.points ⊆ B.erase z := by
    intro i hi
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_erase.mpr ⟨hout k,(Finset.mem_filter.mp hk).2⟩
  have hcard := Finset.card_le_card himage
  rw [Finset.card_image_of_injective _ C.points.injective,
    Finset.card_erase_of_mem hB.2.2.2,hB.1.1] at hcard
  rw [hs] at hlow
  omega

def Configuration.coordinateEquiv {D : BinaryCode n} (C : Configuration D)
    (hs : Function.Surjective C.points) : Point ≃ Fin n :=
  pointPermutation.symm.trans (Equiv.ofBijective C.points ⟨C.points.injective,hs⟩)

theorem Configuration.card_eq {D : BinaryCode n} (C : Configuration D)
    (hs : Function.Surjective C.points) : n=8 := by
  have h := Fintype.card_congr (C.coordinateEquiv hs)
  simpa using h.symm

theorem Configuration.code_eq {D : BinaryCode n} (C : Configuration D)
    (hD : SelfDual D) (hs : Function.Surjective C.points) (x : BinaryVector n) :
    x∈D ↔ (fun p => x (C.coordinateEquiv hs p))∈code := by
  change x∈D ↔ ∃ a : Param,evaluate a=(fun p => x (C.coordinateEquiv hs p))
  constructor
  · intro hx
    obtain ⟨a,ha⟩ := C.restriction hD x hx
    refine ⟨a,?_⟩
    funext p
    have H := congrFun ha (pointPermutation.symm p)
    simpa [prototype,Configuration.coordinateEquiv] using H
  · rintro ⟨a,ha⟩
    have he : embed C.points (prototype a)=x := by
      funext i
      obtain ⟨k,rfl⟩ := hs i
      rw [embed_apply]
      have H := congrFun ha (pointPermutation k)
      simpa [prototype,Configuration.coordinateEquiv] using H
    rw [←he]
    exact C.prototype_mem a

/-- The stronger structural core needs no separate weight-two exclusion. -/
theorem steiner_reconstruction (D : BinaryCode n) (hn : 4<n)
    (hD : SelfDual D) (hS : SteinerProperty D) :
    n=8 ∧ ∃ e : Point ≃ Fin n,∀ x : BinaryVector n,
      x∈D ↔ (fun p => x (e p))∈code := by
  obtain ⟨C⟩ := configuration_exists D hn hS
  have hs := C.surjective hD hS
  exact ⟨C.card_eq hs,C.coordinateEquiv hs,C.code_eq hD hs⟩

end
end Holant.ReedMuller.Steiner
