import Holant.Pauli.ExoticKlein.SixPortIntegerModel
import Holant.Pauli.ExoticKlein.SixPortResidualAction
import Holant.Pauli.ExoticKlein.SixPortAtlasMatching

/-! An exact Gaussian-integer first-card filter for the960 literal products.
Only the fixed numeric factor two is cleared; no unknown scale or card entry
is divided away in the filter. -/
namespace Holant.Pauli.ExoticKlein.SixPort.Atlas
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators

def evalInteger : GZ →+* ℂ := Algebraic.gaussianToComplex.comp integerToGaussian

theorem evalInteger_injective : Function.Injective evalInteger :=
  Algebraic.gaussianToComplex_injective.comp integerToGaussian_injective

def rawProduct (j : Fin 960) : Signature GZ 6 := productTensorOver integerI (productDirectionEquiv j)

theorem eval_rawProduct (j : Fin 960) (x : Fin 6 → Bool) :
    evalInteger (rawProduct j x) = productTensor (productDirectionEquiv j) x := by
  have hh := congrArg Algebraic.gaussianToComplex (integerProduct_correct j (wordEquiv 6 x))
  simp only [integerProduct,productVector,Equiv.symm_apply_apply] at hh
  rw [map_gaussianProduct] at hh
  exact hh

def doubleBase (j : Fin 960) (w : Fin 16) : GZ :=
  let z := (wordEquiv 4).symm w
  rawProduct j (Fin.cons false (Fin.cons false z)) + rawProduct j (Fin.cons true (Fin.cons true z))

def baseValue (w : Fin 16) : GZ :=
  directionTensorOver integerI baseDirection ((wordEquiv 4).symm w)

theorem eval_baseValue (w : Fin 16) :
    evalInteger (baseValue w) = directionTensor baseDirection ((wordEquiv 4).symm w) := by
  have hh := congrArg Algebraic.gaussianToComplex
    (integerToGaussian_direction baseDirection ((wordEquiv 4).symm w))
  simpa only [evalInteger,RingHom.comp_apply,baseValue,map_gaussianDirection] using hh

theorem baseValue_zero : baseValue 0 = 1 := by decide +kernel

theorem base_pivot : directionTensor baseDirection ((wordEquiv 4).symm 0) = 1 := by
  rw [←eval_baseValue,baseValue_zero,map_one]

theorem eval_doubleBase (j : Fin 960) (w : Fin 16) :
    evalInteger (doubleBase j w) =
      2*baseCard 0 (productTensor (productDirectionEquiv j)) ((wordEquiv 4).symm w) := by
  simp only [doubleBase,map_add,eval_rawProduct,baseCard,Fintype.sum_bool,
    dual_apply,theta_zero,d_zero,E_zero]
  norm_num
  ring

def Good (j : Fin 960) : Prop := doubleBase j 0 ≠ 0 ∧ ∀ w, doubleBase j w = doubleBase j 0*baseValue w

instance (j : Fin 960) : Decidable (Good j) := inferInstanceAs (Decidable (_ ∧ _))

def productScale (j : Fin 960) : LinearCertificate.Q := 2/integerToGaussian (doubleBase j 0)

def normalizedProduct (j : Fin 960) : Signature ℂ 6 :=
  fun x => Algebraic.gaussianToComplex (productScale j)*productTensor (productDirectionEquiv j) x

def BaseNormalized (h : Signature ℂ 6) : Prop := baseCard 0 h = directionTensor baseDirection

theorem baseNormalized_nonzero (h : Signature ℂ 6) (hh : BaseNormalized h) : h ≠ 0 := by
  intro hz
  have hv := congrFun hh ((wordEquiv 4).symm 0)
  rw [hz,base_pivot] at hv
  simp only [baseCard,Pi.zero_apply,mul_zero,Finset.sum_const_zero] at hv
  exact zero_ne_one hv

theorem productScale_eval (j : Fin 960) :
    Algebraic.gaussianToComplex (productScale j) = 2/evalInteger (doubleBase j 0) := by
  simp only [productScale,map_div₀,map_ofNat,evalInteger,RingHom.comp_apply]

/-- Any arbitrary complex multiple with the stipulated first card passes the
literal integer filter, and its scale is forced exactly. -/
theorem normalized_scaled_product (j : Fin 960) (c : ℂ) (hc : c ≠ 0)
    (hn : BaseNormalized (fun x => c*productTensor (productDirectionEquiv j) x)) :
    Good j ∧ c = Algebraic.gaussianToComplex (productScale j) := by
  have hcard (w : Fin 16) : c*evalInteger (doubleBase j w) = 2*evalInteger (baseValue w) := by
    have hh := congrFun hn ((wordEquiv 4).symm w)
    rw [baseCard_scale] at hh
    rw [eval_doubleBase,eval_baseValue]
    change c*baseCard 0 (productTensor (productDirectionEquiv j)) ((wordEquiv 4).symm w) = _ at hh
    linear_combination 2*hh
  have hp : c*evalInteger (doubleBase j 0) = 2 := by
    simpa only [baseValue_zero,map_one,mul_one] using hcard 0
  have hp0 : evalInteger (doubleBase j 0) ≠ 0 := by
    intro h
    rw [h,mul_zero] at hp
    norm_num at hp
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro hz
    exact hp0 (by rw [hz,map_zero])
  · intro w
    apply evalInteger_injective
    rw [map_mul]
    apply mul_left_cancel₀ hc
    rw [hcard,←mul_assoc,hp]
  · rw [productScale_eval]
    exact (eq_div_iff hp0).mpr hp

theorem good_normalized (j : Fin 960) (hj : Good j) : BaseNormalized (normalizedProduct j) := by
  have hp : evalInteger (doubleBase j 0) ≠ 0 := fun h => hj.1 (evalInteger_injective (h.trans (map_zero _).symm))
  funext z
  obtain ⟨w,rfl⟩ := (wordEquiv 4).symm.surjective z
  change baseCard 0 (fun x => Algebraic.gaussianToComplex (productScale j)*productTensor (productDirectionEquiv j) x)
    ((wordEquiv 4).symm w) = _
  rw [baseCard_scale,productScale_eval]
  have he := eval_doubleBase j w
  rw [hj.2 w,map_mul,eval_baseValue] at he
  change (2/evalInteger (doubleBase j 0))*baseCard 0 (productTensor (productDirectionEquiv j))
    ((wordEquiv 4).symm w) = _
  apply (mul_left_cancel₀ hp)
  field_simp
  exact he.symm

end
end Holant.Pauli.ExoticKlein.SixPort.Atlas
