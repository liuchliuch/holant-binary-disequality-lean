import Holant.Proofs.Hardness.GeneralEOAffinePlanePower

/-! The finite phase identity is derived from literal affine/nonproduct
conditions, retaining the original coefficient scale. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOAffinePlanePeriod
open Holant Holant.Tractable
open scoped Matrix
namespace P
export GeneralEOAffinePlanePower (Mat normalized normalized_power)
end P
namespace B
export EOBinaryPlaneClassification (Full Cross full_affine_iff full_product_iff)
end B
set_option backward.isDefEq.respectTransparency false
variable (f : Signature AlgebraicComplex 2)

def table : P.Mat := !![f ![false,false],f ![false,true];f ![true,false],f ![true,true]]
def scale : AlgebraicComplex := 4096*(f ![false,false])^24

variable (hf : B.Full f) (hA : Affine f) (hP : ¬Product f)

include hf hA hP in
theorem normal_form : ∃r s : ZMod 4,
    table f=(f ![false,false]) • P.normalized r s := by
  have ha := hf ![false,false]
  obtain ⟨hpow,hcross⟩ := (B.full_affine_iff f hf).mp hA
  have hc : f ![false,false]*f ![true,true]=-(f ![false,true]*f ![true,false]) :=
    hcross.resolve_left (fun h => hP ((B.full_product_iff f hf).mpr h))
  have hr : (f ![true,false]/f ![false,false])^4=1 := by
    rw [div_pow,hpow ![true,false],div_self (pow_ne_zero 4 ha)]
  have hs : (f ![false,true]/f ![false,false])^4=1 := by
    rw [div_pow,hpow ![false,true],div_self (pow_ne_zero 4 ha)]
  obtain ⟨r,hr⟩ := fourthRootPhase_surjective_of_pow_four hr
  obtain ⟨s,hs⟩ := fourthRootPhase_surjective_of_pow_four hs
  have hr' : f ![false,false]*fourthRootPhase r=f ![true,false] := by rw [hr]; field_simp
  have hs' : f ![false,false]*fourthRootPhase s=f ![false,true] := by rw [hs]; field_simp
  have hd : f ![true,true]=-(f ![false,false]*fourthRootPhase r*fourthRootPhase s) := by
    apply mul_left_cancel₀ ha
    rw [hc,←hr',←hs']
    ring
  refine ⟨r,s,?_⟩
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j
  · change f ![false,false]=f ![false,false]*1
    ring
  · change f ![false,true]=f ![false,false]*fourthRootPhase s
    exact hs'.symm
  · change f ![true,false]=f ![false,false]*fourthRootPhase r
    exact hr'.symm
  · change f ![true,true]=f ![false,false]*(-(fourthRootPhase r*fourthRootPhase s))
    rw [hd]
    ring

include hf hA hP in
theorem power : table f^24=scale f • (1 : P.Mat) := by
  obtain ⟨r,s,hr⟩ := normal_form f hf hA hP
  rw [hr,smul_pow,P.normalized_power,smul_smul]
  unfold scale
  congr 1
  ring

include hf in
theorem scale_ne_zero : scale f≠0 :=
  mul_ne_zero (by norm_num) (pow_ne_zero _ (hf ![false,false]))

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOAffinePlanePeriod
