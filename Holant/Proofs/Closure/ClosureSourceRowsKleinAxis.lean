import Holant.Proofs.Closure.ClosureKleinShapeMatrix
import Holant.Certificates.EqualityQuaternary.KleinBasis

/-! NEW UNVERIFIED native-axis consumer geometry. Transfer A=axis(a,b)
produces raw source B=A X, not A. Both raw rows are identified with literal
standard/exotic E2/E3, using nonzero coefficients in the ORIGINAL field L.
No group classifier, basis change, SourceDeck or physical programme is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSourceRowsKleinAxis
open scoped QuadraticAlgebra
open Holant Holant.Tractable Holant.Marked
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureKleinShape
open Holant.Certificates.EqualityQuaternary
variable {L : Type} [Field L]

/-- The right native X exchanges the two axis coefficients in ordered ports. -/
theorem axis_mul_X (a b : L) : axis a b * X = axis b a := by
  ext u v
  cases u <;> cases v <;> simp [axis,X,Signature.disequality,Matrix.mul_apply]

theorem axis_map (φ : L →+* AlgebraicComplex) (a b : L) :
    (axis a b).map φ = axis (φ a) (φ b) := by
  ext u v
  cases u <;> cases v <;> simp [axis,Matrix.map_apply]

theorem neg_axis_map (φ : L →+* AlgebraicComplex) (a b : L) :
    (-(axis a b)).map φ = axis (-(φ a)) (-(φ b)) := by
  ext u v
  cases u <;> cases v <;> simp [axis,Matrix.map_apply]

theorem E_standard_two : Klein.E .standard 2 = axis (1 : AlgebraicComplex) 0 := by
  ext u v
  cases u <;> cases v <;> norm_num [Klein.E,Klein.basisQ,Klein.matrix,axis]

theorem E_standard_three : Klein.E .standard 3 = axis (0 : AlgebraicComplex) 1 := by
  ext u v
  cases u <;> cases v <;> norm_num [Klein.E,Klein.basisQ,Klein.matrix,axis]

theorem E_exotic_two : Klein.E .exotic 2 = axis imaginaryUnit 1 := by
  ext u v
  cases u <;> cases v <;> norm_num [Klein.E,Klein.basisQ,Klein.matrix,Klein.embed_apply,Klein.qI,axis]

theorem E_exotic_three : Klein.E .exotic 3 = axis (-imaginaryUnit) 1 := by
  ext u v
  cases u <;> cases v <;> norm_num [Klein.E,Klein.basisQ,Klein.matrix,Klein.embed_apply,Klein.qI,axis]

/-- The exotic equation is factored in the actual algebraic scalar field.
Its sign is determined relative to literal i; no conjugator is selected. -/
theorem exotic_sign (φ : L →+* AlgebraicComplex) (a b : L) (shape : a^2+b^2=0) :
    φ a = imaginaryUnit * φ b ∨ φ a = -(imaginaryUnit * φ b) := by
  have hs : (φ a)^2+(φ b)^2=0 := by simpa only [map_add,map_pow,map_zero] using congrArg φ shape
  have hsq : (φ a)^2 = (imaginaryUnit * φ b)^2 := by
    calc
      (φ a)^2 = -(φ b)^2 := eq_neg_of_add_eq_zero_left hs
      _ = (imaginaryUnit * φ b)^2 := by rw [mul_pow,imaginaryUnit_sq]; ring
  exact sq_eq_sq_iff_eq_or_eq_neg.mp hsq

theorem exotic_nonzero (a b : L) (nonsingular : Matrix.det (axis a b) ≠ 0)
    (shape : a^2+b^2=0) : a ≠ 0 ∧ b ≠ 0 := by
  constructor
  · intro ha
    have hb2 : b^2=0 := by simpa only [ha,zero_pow (by decide : 2 ≠ 0),zero_add] using shape
    have hb : b=0 := (pow_eq_zero_iff (by decide : 2 ≠ 0)).mp hb2
    apply nonsingular
    simp [axis_det,ha,hb]
  · intro hb
    have ha2 : a^2=0 := by simpa only [hb,zero_pow (by decide : 2 ≠ 0),add_zero] using shape
    have ha : a=0 := (pow_eq_zero_iff (by decide : 2 ≠ 0)).mp ha2
    apply nonsingular
    simp [axis_det,ha,hb]

/-- A source-field coefficient for EACH ordered nontrivial literal row. -/
structure RawAxisLines (φ : L →+* AlgebraicComplex) (a b : L) where
  kind : Klein.Kind
  leftIndex : Fin 4
  rightIndex : Fin 4
  leftCoefficient : L
  rightCoefficient : L
  leftNonzero : leftCoefficient ≠ 0
  rightNonzero : rightCoefficient ≠ 0
  indices : (leftIndex=2 ∧ rightIndex=3) ∨ (leftIndex=3 ∧ rightIndex=2)
  left : (axis a b * X).map φ = scale (φ leftCoefficient) (Klein.E kind leftIndex)
  right : (-(axis a b)).map φ = scale (φ rightCoefficient) (Klein.E kind rightIndex)

def standardLeft (φ : L →+* AlgebraicComplex) (a : L) (ha : a ≠ 0) : RawAxisLines φ a 0 := by
  refine ⟨.standard,3,2,a,-a,ha,neg_ne_zero.mpr ha,Or.inr ⟨rfl,rfl⟩,?_,?_⟩
  · rw [axis_mul_X,axis_map,E_standard_three]
    ext u v
    cases u <;> cases v <;> simp [axis,scale]
  · rw [neg_axis_map,E_standard_two]
    ext u v
    cases u <;> cases v <;> simp [axis,scale]

def standardRight (φ : L →+* AlgebraicComplex) (b : L) (hb : b ≠ 0) : RawAxisLines φ 0 b := by
  refine ⟨.standard,2,3,b,-b,hb,neg_ne_zero.mpr hb,Or.inl ⟨rfl,rfl⟩,?_,?_⟩
  · rw [axis_mul_X,axis_map,E_standard_two]
    ext u v
    cases u <;> cases v <;> simp [axis,scale]
  · rw [neg_axis_map,E_standard_three]
    ext u v
    cases u <;> cases v <;> simp [axis,scale]

def exoticPlus (φ : L →+* AlgebraicComplex) (a b : L) (ha : a ≠ 0) (hb : b ≠ 0)
    (sign : φ a = imaginaryUnit * φ b) : RawAxisLines φ a b := by
  refine ⟨.exotic,3,2,a,-b,ha,neg_ne_zero.mpr hb,Or.inr ⟨rfl,rfl⟩,?_,?_⟩
  · rw [axis_mul_X,axis_map,E_exotic_three]
    ext u v
    cases u <;> cases v <;> simp [axis,scale,sign] <;> ring_nf <;> simp [imaginaryUnit_sq]
  · rw [neg_axis_map,E_exotic_two]
    ext u v
    cases u <;> cases v <;> simp [axis,scale,sign] <;> ring_nf <;> simp [imaginaryUnit_sq]

def exoticMinus (φ : L →+* AlgebraicComplex) (a b : L) (ha : a ≠ 0) (hb : b ≠ 0)
    (sign : φ a = -(imaginaryUnit * φ b)) : RawAxisLines φ a b := by
  refine ⟨.exotic,2,3,a,-b,ha,neg_ne_zero.mpr hb,Or.inl ⟨rfl,rfl⟩,?_,?_⟩
  · rw [axis_mul_X,axis_map,E_exotic_two]
    ext u v
    cases u <;> cases v <;> simp [axis,scale,sign] <;> ring_nf <;> simp [imaginaryUnit_sq]
  · rw [neg_axis_map,E_exotic_three]
    ext u v
    cases u <;> cases v <;> simp [axis,scale,sign] <;> ring_nf <;> simp [imaginaryUnit_sq]

/-- The concrete native axis equations choose the literal row, its ordered
indices and ORIGINAL-field coefficients. This helper does not assert those
rows belong to an arbitrary source group; the actual group producer supplies
its selected key and product-key provenance separately. -/
def ofNativeAxis (φ : L →+* AlgebraicComplex) (a b : L)
    (nonsingular : Matrix.det (axis a b) ≠ 0) (shape : a*b=0 ∨ a^2+b^2=0) : RawAxisLines φ a b := by
  classical
  by_cases standard : a*b=0
  · by_cases ha : a=0
    · have hb0 : b ≠ 0 := by
        intro hb
        apply nonsingular
        simp [axis_det,ha,hb]
      exact ha.symm ▸ standardRight φ b hb0
    · have hb : b=0 := (mul_eq_zero.mp standard).resolve_left ha
      exact hb.symm ▸ standardLeft φ a ha
  · have exotic : a^2+b^2=0 := shape.resolve_left standard
    have nonzero := exotic_nonzero a b nonsingular exotic
    by_cases sign : φ a = imaginaryUnit * φ b
    · exact exoticPlus φ a b nonzero.1 nonzero.2 sign
    · exact exoticMinus φ a b nonzero.1 nonzero.2 ((exotic_sign φ a b exotic).resolve_left sign)

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSourceRowsKleinAxis
