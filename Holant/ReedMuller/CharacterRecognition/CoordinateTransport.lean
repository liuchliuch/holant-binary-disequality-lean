import Holant.ReedMuller.AffineRadon.FlatIsometry

/-! Character-flatness under literal analytic affine orthogonal coordinate
changes, nonzero scales and linear signs. These maps are not claimed to be
available physical gadgets. -/
noncomputable section
namespace Holant.ReedMuller.CharacterRecognition
open Holant Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.CharacterFlat Holant.ReedMuller.AffineRadon
set_option backward.isDefEq.respectTransparency false
variable {n m : ℕ}

 def linearSign (ell : Character n) (f : Signature ℂ n) : Signature ℂ n :=
  fun x => sign (ell (vectorWord x))*f x

 theorem nonzeroFlat_linearSign (ell : Character n) (f : Signature ℂ n)
    (hf : NonzeroFlat f) : NonzeroFlat (linearSign ell f) := by
  obtain ⟨c,a,D,chi,hD,rfl⟩ := hf
  refine ⟨c,a,D,ell+chi,hD,?_⟩
  funext x
  simp only [linearSign,signature,value,LinearMap.add_apply,sign_add]
  split_ifs <;> ring

 theorem cflat_linearSign (ell : Character n) (f : Signature ℂ n)
    (hf : CFlat f) : CFlat (linearSign ell f) := by
  rcases hf with rfl | hf
  · left; funext x; exact mul_zero _
  · exact Or.inr (nonzeroFlat_linearSign ell f hf)

 theorem linearSign_twice (ell : Character n) (f : Signature ℂ n) :
    linearSign ell (linearSign ell f)=f := by
  funext x
  simp only [linearSign,←mul_assoc,sign_square,one_mul]

 theorem cflat_linearSign_iff (ell : Character n) (f : Signature ℂ n) :
    CFlat (linearSign ell f) ↔ CFlat f := by
  constructor
  · intro h
    have hh := cflat_linearSign ell _ h
    rwa [linearSign_twice] at hh
  · exact cflat_linearSign ell f

 theorem nonzeroFlat_affineIsometryPullback (L : BinaryVector n ≃ₗ[ZMod 2] BinaryVector m)
    (hL : ∀x y,dot (L x) (L y)=dot x y) (b : BinaryVector m)
    (f : Signature ℂ n) (hf : NonzeroFlat f) : NonzeroFlat (affineIsometryPullback L b f) := by
  obtain ⟨c,a,D,ell,hD,rfl⟩ := hf
  refine ⟨c*Units.mk0 (sign (-ell (L.symm b))) (sign_nonzero _),
    b+L a,D.map L.toLinearMap,ell.comp L.symm.toLinearMap,
    selfDual_linearImage L hL D hD,?_⟩
  funext x
  have he : L.symm (vectorWord x-b)-a=L.symm (vectorWord x-(b+L a)) := by
    simp only [sub_add_eq_sub_sub,map_sub,L.symm_apply_apply]
  simp only [affineIsometryPullback,signature,value,FlatNetwork.vector_word,Units.val_mul,
    Units.val_mk0,LinearMap.comp_apply,LinearEquiv.coe_coe]
  rw [FlatNetwork.vector_word,he]
  rw [mem_linearImage L D]
  have hp : sign (ell (L.symm (vectorWord x-b)))=
      sign (ell (L.symm (vectorWord x)))*sign (-ell (L.symm b)) := by
    rw [map_sub,map_sub,sub_eq_add_neg,sign_add]
  rw [hp]
  split_ifs <;> ring

 theorem cflat_affineIsometryPullback (L : BinaryVector n ≃ₗ[ZMod 2] BinaryVector m)
    (hL : ∀x y,dot (L x) (L y)=dot x y) (b : BinaryVector m)
    (f : Signature ℂ n) (hf : CFlat f) : CFlat (affineIsometryPullback L b f) := by
  rcases hf with rfl | hf
  · exact Or.inl rfl
  · exact Or.inr (nonzeroFlat_affineIsometryPullback L hL b f hf)

 theorem affineIsometryPullback_inverse (L : BinaryVector n ≃ₗ[ZMod 2] BinaryVector m)
    (b : BinaryVector m) (f : Signature ℂ n) :
    affineIsometryPullback L.symm (-L.symm b) (affineIsometryPullback L b f)=f := by
  funext x
  simp only [affineIsometryPullback,LinearEquiv.symm_symm,FlatNetwork.vector_word,map_sub,map_neg,
    L.apply_symm_apply,sub_neg_eq_add,add_sub_cancel_right,L.symm_apply_apply,FlatNetwork.word_vector]

 theorem cflat_affineIsometryPullback_iff (L : BinaryVector n ≃ₗ[ZMod 2] BinaryVector m)
    (hL : ∀x y,dot (L x) (L y)=dot x y) (b : BinaryVector m)
    (f : Signature ℂ n) : CFlat (affineIsometryPullback L b f) ↔ CFlat f := by
  constructor
  · intro h
    have hinv (x y : BinaryVector m) : dot (L.symm x) (L.symm y)=dot x y := by
      simpa only [L.apply_symm_apply] using (hL (L.symm x) (L.symm y)).symm
    have hh := cflat_affineIsometryPullback L.symm hinv (-L.symm b) _ h
    rwa [affineIsometryPullback_inverse] at hh
  · exact cflat_affineIsometryPullback L hL b f

 theorem cflat_smul_iff (c : ℂ) (hc : c≠0) (f : Signature ℂ n) : CFlat (c • f) ↔ CFlat f := by
  constructor
  · intro h
    have hh := h.smul _ c⁻¹
    rwa [smul_smul,inv_mul_cancel₀ hc,one_smul] at hh
  · exact fun h => h.smul f c

 def coordinateTransform (L : BinaryVector n ≃ₗ[ZMod 2] BinaryVector m)
    (b : BinaryVector m) (c : ℂ) (ell : Character m) (f : Signature ℂ n) : Signature ℂ m :=
  c • linearSign ell (affineIsometryPullback L b f)

 theorem cflat_coordinateTransform_iff (L : BinaryVector n ≃ₗ[ZMod 2] BinaryVector m)
    (hL : ∀x y,dot (L x) (L y)=dot x y) (b : BinaryVector m) (c : ℂ) (hc : c≠0)
    (ell : Character m) (f : Signature ℂ n) : CFlat (coordinateTransform L b c ell f) ↔ CFlat f := by
  rw [coordinateTransform,cflat_smul_iff c hc,cflat_linearSign_iff,
    cflat_affineIsometryPullback_iff L hL]

end Holant.ReedMuller.CharacterRecognition
