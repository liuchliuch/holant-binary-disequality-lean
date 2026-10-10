import Holant.ReedMuller.CharacterFlat.Tensor

/-! Flatness under a proved affine isometry of actual binary coordinate
spaces. This is an analytic coordinate identity, not a free physical gadget. -/
namespace Holant.ReedMuller.AffineRadon
open Holant Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n m : ℕ}

 theorem mem_linearImage (L : BinaryVector n ≃ₗ[ZMod 2] BinaryVector m)
    (D : BinaryCode n) (x : BinaryVector m) :
    x∈D.map L.toLinearMap ↔ L.symm x∈D := by
  constructor
  · rintro ⟨y,hy,hx⟩
    change L y=x at hx
    rw [←hx,L.symm_apply_apply]
    exact hy
  · intro hx
    exact ⟨L.symm x,hx,L.apply_symm_apply x⟩

 theorem selfDual_linearImage (L : BinaryVector n ≃ₗ[ZMod 2] BinaryVector m)
    (hL : ∀ x y,dot (L x) (L y)=dot x y) (D : BinaryCode n) (hD : SelfDual D) :
    SelfDual (D.map L.toLinearMap) := by
  intro x
  rw [mem_linearImage]
  constructor
  · intro hx y hy
    have hy' := (mem_linearImage L D y).mp hy
    have H := (hD _).mp hx _ hy'
    rw [←hL,L.apply_symm_apply,L.apply_symm_apply] at H
    exact H
  · intro hx
    apply (hD _).mpr
    intro y hy
    have hm : L y∈D.map L.toLinearMap := ⟨y,hy,rfl⟩
    have H := hx (L y) hm
    rw [←L.apply_symm_apply x,hL] at H
    exact H

 def affineIsometryPullback (L : BinaryVector n ≃ₗ[ZMod 2] BinaryVector m)
    (b : BinaryVector m) (f : Signature ℂ n) : Signature ℂ m :=
  fun x => f (wordVector (L.symm (vectorWord x-b)))

 theorem flat_affineIsometryPullback (L : BinaryVector n ≃ₗ[ZMod 2] BinaryVector m)
    (hL : ∀ x y,dot (L x) (L y)=dot x y) (b : BinaryVector m)
    (f : Signature ℂ n) (hf : Flat f) : Flat (affineIsometryPullback L b f) := by
  obtain ⟨c,a,D,hD,rfl⟩ := hf
  refine ⟨c,b+L a,D.map L.toLinearMap,selfDual_linearImage L hL D hD,?_⟩
  funext x
  have he : L.symm (vectorWord x-b)-a=L.symm (vectorWord x-(b+L a)) := by
    simp only [sub_add_eq_sub_sub,map_sub,L.symm_apply_apply]
  change (if (fun i => bit (wordVector (L.symm (vectorWord x-b)) i)-a i)∈D then (c:ℂ) else 0)=
    if (fun i => bit (x i)-(b+L a) i)∈D.map L.toLinearMap then (c:ℂ) else 0
  have hw : (fun i => bit (wordVector (L.symm (vectorWord x-b)) i)-a i)=L.symm (vectorWord x-b)-a := by
    have H := vector_word (L.symm (vectorWord x-b))
    exact congrArg (fun y => y-a) H
  rw [hw,he]
  change (if L.symm (vectorWord x-(b+L a))∈D then (c:ℂ) else 0)=
    if vectorWord x-(b+L a)∈D.map L.toLinearMap then (c:ℂ) else 0
  simp only [mem_linearImage]

 theorem flatOrZero_affineIsometryPullback (L : BinaryVector n ≃ₗ[ZMod 2] BinaryVector m)
    (hL : ∀ x y,dot (L x) (L y)=dot x y) (b : BinaryVector m)
    (f : Signature ℂ n) (hf : FlatOrZero f) : FlatOrZero (affineIsometryPullback L b f) := by
  rcases hf with rfl | hf
  · exact Or.inl rfl
  · exact Or.inr (flat_affineIsometryPullback L hL b f hf)

end
end Holant.ReedMuller.AffineRadon
