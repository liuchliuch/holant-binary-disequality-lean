import Holant.Certificates.OppositeIcosahedral.Directions

namespace Holant.Certificates.OppositeIcosahedral
open Holant Holant.Certificates.MatchingProductBridge
open RainbowOrbit (Proportional)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

def standardRepresentative (i : Fin 60) : Mat := RainbowOrbit.representative .icosahedral i
def oppositeRepresentative (i : Fin 60) : Mat := conjugate (standardRepresentative i)
def kernelIndex (i : Fin 60) : Fin 60 := RainbowOrbit.productIndex .icosahedral ⟨3,by decide⟩ i
def kernelScale (i : Fin 60) : ℂ := (-1/2 : ℂ)*(RainbowOrbit.productScale .icosahedral ⟨3,by decide⟩ i : ℂ)

theorem standardRepresentative_Q3 : standardRepresentative 3=Matrix.of Q3 := by
  ext a b
  cases a <;> cases b <;>
    simp [standardRepresentative,RainbowOrbit.representative,RainbowOrbit.raw,RainbowOrbit.icosahedralRaw,
      RainbowOrbit.goldenMatrix,RainbowOrbit.GoldenInt.eval,quaternion,Q0,Q1,Q2,Q3,Signature.equality]

theorem standardRepresentative_mem (i : Fin 60) : groupDirection .icosahedral (standardRepresentative i) :=
  RainbowOrbit.representative_mem .icosahedral i

theorem oppositeRepresentative_mem (i : Fin 60) : Direction (oppositeRepresentative i) :=
  conjugate_standard (standardRepresentative_mem i)

theorem oppositeRepresentative_det (i : Fin 60) : (oppositeRepresentative i).det≠0 :=
  (oppositeRepresentative_mem i).det_ne_zero

theorem direction_complete (U : Mat) : Direction U ↔
    ∃i : Fin 60,∃c : ℂ,c≠0 ∧ U=c • oppositeRepresentative i := by
  rw [direction_iff_conjugate]
  constructor
  · rintro ⟨V,hV,rfl⟩
    obtain ⟨i,c,hc,he⟩ := (RainbowOrbit.complete .icosahedral V).mp hV
    change V=c • standardRepresentative i at he
    rw [he,conjugate_smul]
    exact ⟨i,c,hc,rfl⟩
  · rintro ⟨i,c,hc,rfl⟩
    exact ⟨c • standardRepresentative i,groupDirection_smul .icosahedral (standardRepresentative_mem i) hc,
      (conjugate_smul c _).symm⟩

theorem oppositeRepresentative_projectively_injective (i j : Fin 60) (c : ℂ)
    (h : oppositeRepresentative i=c • oppositeRepresentative j) : i=j := by
  have hh := congrArg pull h
  simp only [oppositeRepresentative,pull_smul,pull_conjugate] at hh
  exact RainbowOrbit.projectively_injective .icosahedral i j c hh

theorem kernelScale_ne_zero (i : Fin 60) : kernelScale i≠0 := by
  apply mul_ne_zero (by norm_num : (-1/2 : ℂ)≠0)
  exact Int.cast_ne_zero.mpr (RainbowOrbit.raw_certificate .icosahedral ⟨3,by decide⟩ i).1

/-- All60 actual kernel images, indexed by the already checked left-Q3 table,
with their literal nonzero representative scalars. -/
theorem kernel_representative_exact (i : Fin 60) :
    kappa (standardRepresentative i)=kernelScale i • oppositeRepresentative (kernelIndex i) := by
  rw [kappa_Q3_dictionary,←standardRepresentative_Q3]
  have hh := RainbowOrbit.mul_exact .icosahedral ⟨3,by decide⟩ i
  change standardRepresentative 3*standardRepresentative i=
    (RainbowOrbit.productScale .icosahedral ⟨3,by decide⟩ i : ℂ) • standardRepresentative (kernelIndex i) at hh
  rw [hh,conjugate_smul,smul_smul]
  rfl

theorem kernelIndex_bijective : Function.Bijective kernelIndex := by decide +kernel

def kernelClassIndexEquiv : Fin 60≃Fin 60 := Equiv.ofBijective kernelIndex kernelIndex_bijective

theorem kappa_injective : Function.Injective kappa := by
  intro U V h
  have hh := congrArg unkappa h
  simpa only [unkappa_kappa] using hh

theorem kernel_membership_iff (U : Mat) :
    Direction (kappa U) ↔ groupDirection .icosahedral U := by
  constructor
  · intro h
    obtain ⟨i,c,hc,he⟩ := (direction_complete _).mp h
    obtain ⟨j,hj⟩ := kernelIndex_bijective.surjective i
    have hU : U=(c/kernelScale j) • standardRepresentative j := by
      apply kappa_injective
      rw [kappa_smul,kernel_representative_exact,hj,smul_smul]
      simpa [div_mul_cancel₀ c (kernelScale_ne_zero j)] using he
    rw [hU]
    exact groupDirection_smul .icosahedral (standardRepresentative_mem j) (div_ne_zero hc (kernelScale_ne_zero j))
  · intro h
    obtain ⟨i,c,hc,he⟩ := (RainbowOrbit.complete .icosahedral U).mp h
    change U=c • standardRepresentative i at he
    rw [he,kappa_smul,kernel_representative_exact,smul_smul]
    exact Direction.smul (oppositeRepresentative_mem _) (mul_ne_zero hc (kernelScale_ne_zero i))

theorem kappa_proportional_iff (U V : Mat) :
    Proportional (kappa U) (kappa V) ↔ Proportional U V := by
  constructor
  · rintro ⟨c,hc,he⟩
    exact ⟨c,hc,kappa_injective (by rw [kappa_smul]; exact he)⟩
  · rintro ⟨c,hc,rfl⟩
    exact ⟨c,hc,kappa_smul c V⟩

def standardKernelClass (i : Fin 60) : Projectivization ℂ Mat :=
  Projectivization.mk ℂ (standardRepresentative i) (RainbowOrbit.representative_ne_zero .icosahedral i)

def oppositeKernelClass (i : Fin 60) : Projectivization ℂ Mat :=
  Projectivization.mk ℂ (oppositeRepresentative i) (by
    intro h; exact oppositeRepresentative_det i (by rw [h,Matrix.det_zero]))

theorem kernel_class_exact (i : Fin 60) :
    Projectivization.mk ℂ (kappa (standardRepresentative i)) (by
      intro h; have hh := congrArg unkappa h
      have hz : unkappa 0=0 := by simp [unkappa]
      rw [unkappa_kappa,hz] at hh
      exact RainbowOrbit.representative_ne_zero .icosahedral i hh)=
      oppositeKernelClass (kernelClassIndexEquiv i) :=
  (RainbowOrbit.proportional_point_iff _ _ _ _).mp
    ⟨kernelScale i,kernelScale_ne_zero i,kernel_representative_exact i⟩

end
end Holant.Certificates.OppositeIcosahedral
