import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinHigherNonaffineBasis

/-! Actual four-port Pauli recoupling coefficients, exact support selectors,
and recorded nonzero Gaussian-rational values. -/
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffine
noncomputable section
open scoped BigOperators

def Represents (a : Label) (T : Mat) : Prop := ∃ c : ℂ, c ≠ 0 ∧ T = scale c (E a)

theorem represents_E (a : Label) : Represents a (E a) := ⟨1,one_ne_zero,by funext x y; simp [scale]⟩
theorem represents_dual (a : Label) : Represents (theta a) (dual a) :=
  ⟨(d a)⁻¹,inv_ne_zero (d_ne_zero a),rfl⟩

theorem Represents.transpose {a : Label} {T : Mat} (h : Represents a T) :
    Represents (theta a) (Kernel.transpose T) := by
  obtain ⟨c,hc,rfl⟩ := h
  refine ⟨c*transposeScalar a,mul_ne_zero hc (transposeScalar_ne_zero a),?_⟩
  funext x y
  have hh := congrFun (congrFun (transpose_E a) x) y
  change E a y x = transposeScalar a*E (theta a) x y at hh
  simp only [Kernel.transpose_apply,scale,hh]
  ring

theorem Represents.mul {a b : Label} {T U : Mat} (hT : Represents a T) (hU : Represents b U) :
    Represents (a+b) (Kernel.mul T U) := by
  obtain ⟨c,hc,rfl⟩ := hT
  obtain ⟨d,hd,rfl⟩ := hU
  refine ⟨c*d*omega a b,mul_ne_zero (mul_ne_zero hc hd) (omega_ne_zero a b),?_⟩
  funext x y
  have hh := congrFun (congrFun (fusion a b) x) y
  simp only [Kernel.mul_apply,scale] at hh ⊢
  calc
    _ = c*d*(E a x false*E b false y+E a x true*E b true y) := by ring
    _ = _ := by rw [hh]; ring

theorem Represents.trace_ne_zero_iff {a : Label} {T : Mat} (h : Represents a T) :
    Kernel.trace T ≠ 0 ↔ a = 0 := by
  obtain ⟨c,hc,rfl⟩ := h
  have ht : Kernel.trace (scale c (E a)) = c*Kernel.trace (E a) := by
    simp only [Kernel.trace,scale,Fintype.sum_bool]
    ring
  rw [ht,trace_E]
  by_cases ha : a = 0
  · simp [ha,hc,-label_zero]
  · simp [ha,-label_zero]

theorem add_eq_zero_iff (a b : Label) : a+b = 0 ↔ a = b := by
  constructor
  · intro h
    calc
      a = (a+b)+b := by rw [add_assoc,label_add_self,add_zero]
      _ = b := by rw [h,zero_add]
  · rintro rfl; exact label_add_self _

def deltaCross (a b g : Label) : Label := theta g+b+theta a
def deltaParallel (a b g : Label) : Label := g+theta (b+theta a)

/-- Source trace formula for the actual13|24 coefficient in the12|34 basis. -/
theorem cross_coefficient_trace (a b g d : Label) :
    coefficient (cross a b) g d =
      Kernel.trace (Kernel.mul (Kernel.transpose (dual d))
        (Kernel.mul (Kernel.transpose (E a)) (Kernel.mul (dual g) (E b)))) := by
  simp only [coefficient,coefficientOver,Kernel.pair,firstCardOver,cross,crossOver,E,dual,
    Kernel.trace,Kernel.mul,Fintype.sum_bool,Kernel.transpose_apply]
  ring

/-- Source trace formula for the actual14|23 coefficient in the12|34 basis. -/
theorem parallel_coefficient_trace (a b g d : Label) :
    coefficient (parallel a b) g d =
      Kernel.trace (Kernel.mul (Kernel.transpose (dual d))
        (Kernel.mul (Kernel.transpose (E b)) (Kernel.mul (Kernel.transpose (dual g)) (E a)))) := by
  simp only [coefficient,coefficientOver,Kernel.pair,firstCardOver,parallel,parallelOver,E,dual,
    Kernel.trace,Kernel.mul,Fintype.sum_bool,Kernel.transpose_apply]
  ring

/-- Nonzero support follows from fusion and the actual trace rule, not an atlas. -/
theorem cross_coefficient_ne_zero_iff (a b g d : Label) :
    coefficient (cross a b) g d ≠ 0 ↔ d = deltaCross a b g := by
  rw [cross_coefficient_trace]
  have h := ((represents_dual d).transpose.mul
    ((represents_E a).transpose.mul ((represents_dual g).mul (represents_E b)))).trace_ne_zero_iff
  rw [theta_theta] at h
  rw [h]
  have he : d+(theta a+(theta g+b)) = d+deltaCross a b g := by unfold deltaCross; abel
  rw [he,add_eq_zero_iff]

theorem parallel_coefficient_ne_zero_iff (a b g d : Label) :
    coefficient (parallel a b) g d ≠ 0 ↔ d = deltaParallel a b g := by
  rw [parallel_coefficient_trace]
  have h := ((represents_dual d).transpose.mul
    ((represents_E b).transpose.mul ((represents_dual g).transpose.mul (represents_E a)))).trace_ne_zero_iff
  simp only [theta_theta] at h
  rw [h]
  have he : d+(theta b+(g+a)) = d+deltaParallel a b g := by
    unfold deltaParallel
    rw [theta_add,theta_theta]
    abel
  rw [he,add_eq_zero_iff]

def rhoCross (a b g : Label) : ℂ := coefficient (cross a b) g (deltaCross a b g)
def rhoParallel (a b g : Label) : ℂ := coefficient (parallel a b) g (deltaParallel a b g)

@[simp] theorem rhoCross_ne_zero (a b g : Label) : rhoCross a b g ≠ 0 :=
  (cross_coefficient_ne_zero_iff a b g _).mpr rfl
@[simp] theorem rhoParallel_ne_zero (a b g : Label) : rhoParallel a b g ≠ 0 :=
  (parallel_coefficient_ne_zero_iff a b g _).mpr rfl

/-- Exact13|24 expansion with every original scalar retained. -/
theorem recoupling_cross (a b : Label) (x y z w : Bool) :
    cross a b x y z w = ∑ g : Label, rhoCross a b g*base g (deltaCross a b g) x y z w := by
  rw [← reconstruction (cross a b) x y z w]
  apply Finset.sum_congr rfl
  intro g hg
  apply Finset.sum_eq_single (deltaCross a b g)
  · intro d hd hne
    have hz : coefficient (cross a b) g d = 0 := by
      by_contra h
      exact hne ((cross_coefficient_ne_zero_iff a b g d).mp h)
    simp [hz]
  · simp

/-- Exact14|23 expansion, including the source theta orientation correction. -/
theorem recoupling_parallel (a b : Label) (x y z w : Bool) :
    parallel a b x y z w = ∑ g : Label, rhoParallel a b g*base g (deltaParallel a b g) x y z w := by
  rw [← reconstruction (parallel a b) x y z w]
  apply Finset.sum_congr rfl
  intro g hg
  apply Finset.sum_eq_single (deltaParallel a b g)
  · intro d hd hne
    have hz : coefficient (parallel a b) g d = 0 := by
      by_contra h
      exact hne ((parallel_coefficient_ne_zero_iff a b g d).mp h)
    simp [hz]
  · simp

def gaussianCoefficient (T : Four Algebraic.GaussianRational) (a b : Label) : Algebraic.GaussianRational :=
  coefficientOver gaussianI T a b

theorem map_coefficient (T : Four Algebraic.GaussianRational) (a b : Label) :
    Algebraic.gaussianToComplex (gaussianCoefficient T a b) =
      coefficient (fun x y z w => Algebraic.gaussianToComplex (T x y z w)) a b := by
  have hm (c : Label) (x y : Bool) :
      Algebraic.gaussianToComplex (dualOver gaussianI c x y) = dualOver Complex.I c x y := map_gaussianDual c x y
  simp only [gaussianCoefficient,coefficient,coefficientOver,firstCardOver,Kernel.pair,map_sum,map_mul,hm]

def gaussianRhoCross (a b g : Label) : Algebraic.GaussianRational :=
  gaussianCoefficient (crossOver gaussianI a b) g (deltaCross a b g)
def gaussianRhoParallel (a b g : Label) : Algebraic.GaussianRational :=
  gaussianCoefficient (parallelOver gaussianI a b) g (deltaParallel a b g)

@[simp] theorem map_gaussianRhoCross (a b g : Label) :
    Algebraic.gaussianToComplex (gaussianRhoCross a b g) = rhoCross a b g := by
  rw [gaussianRhoCross,map_coefficient]
  have hm (c : Label) (x y : Bool) :
      Algebraic.gaussianToComplex (EOver gaussianI c x y) = EOver Complex.I c x y := map_gaussianE c x y
  simp only [crossOver,map_mul,hm,rhoCross,cross]
  rfl

@[simp] theorem map_gaussianRhoParallel (a b g : Label) :
    Algebraic.gaussianToComplex (gaussianRhoParallel a b g) = rhoParallel a b g := by
  rw [gaussianRhoParallel,map_coefficient]
  have hm (c : Label) (x y : Bool) :
      Algebraic.gaussianToComplex (EOver gaussianI c x y) = EOver Complex.I c x y := map_gaussianE c x y
  simp only [parallelOver,map_mul,hm,rhoParallel,parallel]
  rfl

/-- Every coefficient has an actual exact Gaussian-rational nonzero witness. -/
theorem rhoCross_gaussian_nonzero (a b g : Label) :
    ∃ q : Algebraic.GaussianRational, q ≠ 0 ∧ Algebraic.gaussianToComplex q = rhoCross a b g := by
  refine ⟨gaussianRhoCross a b g,?_,map_gaussianRhoCross a b g⟩
  intro h
  have hh := map_gaussianRhoCross a b g
  rw [h,map_zero] at hh
  exact rhoCross_ne_zero a b g hh.symm

theorem rhoParallel_gaussian_nonzero (a b g : Label) :
    ∃ q : Algebraic.GaussianRational, q ≠ 0 ∧ Algebraic.gaussianToComplex q = rhoParallel a b g := by
  refine ⟨gaussianRhoParallel a b g,?_,map_gaussianRhoParallel a b g⟩
  intro h
  have hh := map_gaussianRhoParallel a b g
  rw [h,map_zero] at hh
  exact rhoParallel_ne_zero a b g hh.symm

end
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffine
