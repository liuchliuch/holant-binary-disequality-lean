import Holant.Certificates.PlatonicIncidence.BaseCertificate
import Mathlib.LinearAlgebra.Matrix.Bilinear

namespace Holant.Certificates.PlatonicIncidence
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
noncomputable section
set_option backward.isDefEq.respectTransparency false

def leftEquiv (A : Mat) (hA : A.det≠0) : Mat ≃ₗ[ℂ] Mat where
  toFun := fun U => A*U
  invFun := fun U => A⁻¹*U
  left_inv U := by
    change A⁻¹*(A*U)=U
    rw [←mul_assoc,Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hA),one_mul]
  right_inv U := by
    change A*(A⁻¹*U)=U
    rw [←mul_assoc,Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hA),one_mul]
  map_add' U V := mul_add A U V
  map_smul' c U := Matrix.mul_smul A c U

@[simp] theorem leftEquiv_apply (A : Mat) (hA : A.det≠0) (U : Mat) :
    leftEquiv A hA U=A*U := rfl

theorem equiv_span_pair {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (e : V ≃ₗ[ℂ] W) (u v w : V) :
    e w∈Submodule.span ℂ ({e u,e v} : Set W) ↔ w∈Submodule.span ℂ ({u,v} : Set V) := by
  constructor
  · intro h
    obtain ⟨a,b,he⟩ := Submodule.mem_span_pair.mp h
    apply Submodule.mem_span_pair.mpr
    exact ⟨a,b,e.injective (by simpa only [map_add,map_smul] using he)⟩
  · intro h
    obtain ⟨a,b,rfl⟩ := Submodule.mem_span_pair.mp h
    exact Submodule.mem_span_pair.mpr ⟨a,b,by simp only [map_add,map_smul]⟩

theorem span_pair_scaled (a b : ℂ) (ha : a≠0) (hb : b≠0) (U V : Mat) :
    Submodule.span ℂ ({a • U,b • V} : Set Mat)=Submodule.span ℂ ({U,V} : Set Mat) := by
  have h (x y : Mat) : ({x,y} : Set Mat)={x}∪{y} := rfl
  rw [h,h,Submodule.span_union,Submodule.span_union,
    Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr ha),
    Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hb)]

/-- A generic algebraic transport lemma keeps concrete finite dictionaries out
of elaboration of the scalar/span calculation. -/
theorem mul_span_scaled_iff (A U V P Q : Mat) (hA : A.det≠0)
    (c d : ℂ) (hc : c≠0) (hd : d≠0) (hU : A*U=c • P) (hV : A*V=d • Q) :
    Q∈Submodule.span ℂ ({A,P} : Set Mat) ↔
      V∈Submodule.span ℂ ({(1 : Mat),U} : Set Mat) := by
  have h := equiv_span_pair (leftEquiv A hA) (1 : Mat) U V
  simp only [leftEquiv_apply,mul_one,hU,hV] at h
  have hp := span_pair_scaled 1 c one_ne_zero hc A P
  simp only [one_smul] at hp
  rw [hp,Submodule.smul_mem_iff _ hd] at h
  exact h

theorem left_product_injective (g : PlatonicModel) (i : Fin (size g)) :
    Function.Injective (productIndex g i) := by
  intro j k h
  have hs (a : Fin (size g)) : (productScale g i a : ℂ)≠0 :=
    Int.cast_ne_zero.mpr (raw_certificate g i a).1
  have he : representative g i*representative g j=
      ((productScale g i j : ℂ)/(productScale g i k : ℂ)) •
        (representative g i*representative g k) := by
    rw [mul_exact,mul_exact,h,smul_smul,div_mul_cancel₀ _ (hs k)]
  have he' : representative g j=
      ((productScale g i j : ℂ)/(productScale g i k : ℂ)) • representative g k := by
    apply (leftEquiv _ (representative_det_ne_zero g i)).injective
    simpa only [leftEquiv_apply,Matrix.mul_smul] using he
  exact projectively_injective g j k _ he'

def leftPermutation (g : PlatonicModel) (i : Fin (size g)) : Equiv.Perm (Fin (size g)) :=
  Equiv.ofBijective (productIndex g i) ⟨left_product_injective g i,Finite.surjective_of_injective (left_product_injective g i)⟩

@[simp] theorem leftPermutation_apply (g : PlatonicModel) (i j : Fin (size g)) :
    leftPermutation g i j=productIndex g i j := rfl

theorem product_identity_right (g : PlatonicModel) (i : Fin (size g)) :
    productIndex g i (identityIndex g)=i := by
  have h := mul_exact g i (identityIndex g)
  rw [representative_identity,mul_one] at h
  exact (projectively_injective g i _ _ h).symm

end
end Holant.Certificates.PlatonicIncidence
