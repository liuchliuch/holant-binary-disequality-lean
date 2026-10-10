import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.SimpleRing.Basic


namespace Holant.LocalDrafts.MainChain.TransformRecognition.CoefficientIdeal
open MvPolynomial
noncomputable section
variable {K E σ : Type*} [Field K] [Field E] [Algebra K E]

def scalarRetract : E →ₗ[K] K := (Algebra.linearMap K E).leftInverse

theorem scalarRetract_map (a : K) : scalarRetract (algebraMap K E a) = a := by
  exact LinearMap.leftInverse_apply_of_inj
    (LinearMap.ker_eq_bot.mpr (algebraMap K E).injective) a

theorem scalarRetract_mul_map (c : E) (a : K) :
    scalarRetract (c * algebraMap K E a) = scalarRetract (E:=E) c * a := by
  rw [mul_comm]
  rw [← Algebra.smul_def]
  rw [map_smul]
  exact mul_comm a _

def retract : MvPolynomial σ E →+ MvPolynomial σ K :=
  AddMonoidAlgebra.coeffAddEquiv.symm.toAddMonoidHom.comp
    ((Finsupp.mapRange.addMonoidHom (scalarRetract (K:=K) (E:=E)).toAddMonoidHom).comp
      AddMonoidAlgebra.coeffAddEquiv.toAddMonoidHom)

@[simp] theorem retract_monomial (d : σ →₀ ℕ) (c : E) :
    retract (K:=K) (monomial d c) = monomial d (scalarRetract (K:=K) c) := by
  change AddMonoidAlgebra.ofCoeff
    (Finsupp.mapRange (scalarRetract (K:=K) (E:=E)) (map_zero _) (Finsupp.single d c)) = _
  rw [Finsupp.mapRange_single]
  rfl

@[simp] theorem retract_map (p : MvPolynomial σ K) :
    retract (map (algebraMap K E) p) = p := by
  induction p using MvPolynomial.induction_on' with
  | monomial d c => simp [scalarRetract_map]
  | add p q hp hq => simp [hp,hq]

@[simp] theorem retract_one : retract (K:=K) (1 : MvPolynomial σ E) = 1 := by
  simpa only [map_one] using (retract_map (E:=E) (1 : MvPolynomial σ K))

/-- The retraction need not preserve products of arbitrary extension-valued
polynomials. It preserves multiplication by a polynomial over the BASE field,
which is exactly what descending an ideal certificate needs. -/
theorem retract_mul_map (q : MvPolynomial σ E) (p : MvPolynomial σ K) :
    retract (q * map (algebraMap K E) p) = retract q * p := by
  induction q using MvPolynomial.induction_on' with
  | monomial d c =>
    induction p using MvPolynomial.induction_on' with
    | monomial e a =>
      simp only [map_monomial,monomial_mul_monomial,retract_monomial,
        scalarRetract_mul_map]
    | add p q hp hq => simp only [map_add,mul_add,hp,hq]
  | add q r hq hr => simp only [add_mul,map_add,hq,hr]

/-- Multipliers are universally quantified so this is an E-polynomial ideal,
despite coefficient retraction being merely K-linear. -/
def certificateIdeal (I : Ideal (MvPolynomial σ K)) : Ideal (MvPolynomial σ E) where
  carrier := {p | ∀ q, retract (q*p) ∈ I}
  zero_mem' := by intro q; simp
  add_mem' := by
    intro p r hp hr q
    simpa only [mul_add,map_add] using I.add_mem (hp q) (hr q)
  smul_mem' := by
    intro c p hp q
    change retract (q * (c*p)) ∈ I
    simpa only [mul_assoc] using hp (q*c)

theorem map_le_certificateIdeal (I : Ideal (MvPolynomial σ K)) :
    I.map (map (algebraMap K E)) ≤ certificateIdeal I := by
  apply Ideal.map_le_iff_le_comap.mpr
  intro p hp
  change ∀ q, retract (q * map (algebraMap K E) p) ∈ I
  intro q
  rw [retract_mul_map]
  exact I.mul_mem_left _ hp

/-- An actual extension-field ideal certificate projects to a base-field
certificate. No algebraic closure, finiteness or effective witness is assumed. -/
theorem mem_map_iff (I : Ideal (MvPolynomial σ K)) (p : MvPolynomial σ K) :
    map (algebraMap K E) p ∈ I.map (map (algebraMap K E)) ↔ p ∈ I := by
  constructor
  · intro h
    have hp := map_le_certificateIdeal I h (1 : MvPolynomial σ E)
    simpa only [one_mul,retract_map] using hp
  · intro h
    exact Ideal.mem_map_of_mem (map (algebraMap K E)) h

theorem map_eq_top_iff (I : Ideal (MvPolynomial σ K)) :
    I.map (map (algebraMap K E)) = ⊤ ↔ I = ⊤ := by
  rw [Ideal.eq_top_iff_one,Ideal.eq_top_iff_one]
  simpa only [map_one] using mem_map_iff (E:=E) I 1

theorem map_ne_top_iff (I : Ideal (MvPolynomial σ K)) :
    I.map (map (algebraMap K E)) ≠ ⊤ ↔ I ≠ ⊤ :=
  not_congr (map_eq_top_iff I)

/-- This is the exact bridge needed between a number-field sparse ideal
decision and the shared-matrix equations interpreted over AlgebraicComplex. -/
theorem span_map_ne_top_iff {ι : Type*} (equations : ι → MvPolynomial σ K) :
    Ideal.span (Set.range (fun i => map (algebraMap K E) (equations i))) ≠ ⊤ ↔
      Ideal.span (Set.range equations) ≠ ⊤ := by
  simpa only [Ideal.map_span,Set.range_comp'] using
    map_ne_top_iff (E:=E) (Ideal.span (Set.range equations))

end
end Holant.LocalDrafts.MainChain.TransformRecognition.CoefficientIdeal
