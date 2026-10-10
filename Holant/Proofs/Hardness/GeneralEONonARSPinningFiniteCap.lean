import Holant.Proofs.Hardness.FiniteCapLocal
import Holant.Proofs.Hardness.GeneralEOOriginalCapSource

/-! The complete non-resonant branch for arbitrary-arity one-original-row
native binary caps. The frozen finite torsion exponent is reused from
FiniteCapLocal. One finite comparison of literal original coefficient sums
replaces the unequal-norm condition and supplies the actual global pinning
programme, including equal-modulus infinite phases. This does not assert that
every non-ARS row has such a cap, or cover zero-sided caps. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEONonARSPinningFiniteCap
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
namespace Cap
export GeneralEOOriginalCapSource
  (coefficient cap_value original original_eo presentation Input inputEncoding pinValue targetEncoding Choice)
end Cap
namespace I
export GeneralEOOriginalCapInterpolation (p q source)
end I
namespace O
export Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalTarget
  (coefficients coefficients_algebraic originalField originalValue)
end O
namespace Bound
export Holant.Projective.BoundedTorsion (torsionExponent torsionExponent_pos)
end Bound
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local irreducible] GeneralEOOriginalCapInterpolation.source
variable {s r : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance originalAlgebra : Algebra ℚ (O.originalField G) := (O.originalField G).algebra'
local instance originalFinite : FiniteDimensional ℚ (O.originalField G) :=
  familyField_finiteDimensional (O.coefficients G) (O.coefficients_algebraic G)

/-- A single fixed exponent for every original-row cap of this dictionary. -/
def exponent : ℕ := Bound.torsionExponent (Module.finrank ℚ (O.originalField G))

theorem exponent_pos : 0<exponent G := Bound.torsionExponent_pos _

variable (j : Fin s) (e : Fin (a j.val) ≃ (Fin 2 ⊕ (Fin r × Bool)))

def Coefficients : Prop := Cap.coefficient G j e ![false,true]≠0 ∧
  Cap.coefficient G j e ![true,false]≠0 ∧
  Cap.coefficient G j e ![false,true]^exponent G≠
    Cap.coefficient G j e ![true,false]^exponent G

private theorem nonzero (x : Fin 2 → Bool) (h : Cap.coefficient G j e x≠0) :
    GeneralEOOriginalCapInterpolation.cap (Cap.original G) j e x≠0 := by
  intro hz
  have hv := Cap.cap_value G j e x
  rw [hz] at hv
  exact h hv.symm

/-- The finite ambient coefficient comparison has its exact advertised meaning
in the unchanged original field. No root-of-unity order is supplied. -/
theorem finite_iff_no_resonance (hq : Cap.coefficient G j e ![true,false]≠0) :
    Cap.coefficient G j e ![false,true]^exponent G≠
        Cap.coefficient G j e ![true,false]^exponent G ↔
      ∀n : ℕ,0<n → (I.p (Cap.original G) j e/I.q (Cap.original G) j e)^n≠1 := by
  rw [←FiniteCapLocal.coefficient_iff_no_resonance
    (I.p (Cap.original G) j e) (I.q (Cap.original G) j e) (nonzero G j e _ hq)]
  have hleft : (((I.p (Cap.original G) j e)^exponent G : O.originalField G) : AlgebraicComplex)=
      Cap.coefficient G j e ![false,true]^exponent G := by
    change ((GeneralEOOriginalCapInterpolation.cap (Cap.original G) j e ![false,true] :
      O.originalField G) : AlgebraicComplex)^
      exponent G=_
    rw [Cap.cap_value]
  have hright : (((I.q (Cap.original G) j e)^exponent G : O.originalField G) : AlgebraicComplex)=
      Cap.coefficient G j e ![true,false]^exponent G := by
    change ((GeneralEOOriginalCapInterpolation.cap (Cap.original G) j e ![true,false] :
      O.originalField G) : AlgebraicComplex)^
      exponent G=_
    rw [Cap.cap_value]
  change _ ↔ (I.p (Cap.original G) j e)^exponent G≠(I.q (Cap.original G) j e)^exponent G
  rw [←hleft,←hright]
  exact not_congr Subtype.coe_inj

variable (he : Signature.CentralSupport (G j)) (hc : Coefficients G j e)

/-- Arbitrarily many directed01 occurrences are eliminated by the existing
physical cap-chain interpolation machine, using only a finite coefficient test. -/
def source : LengthControlledOracleReduction (Cap.inputEncoding G j e) (Cap.presentation G).encoding
    (Cap.targetEncoding (s:=s) (a:=a)) (Cap.presentation G).encoding
    (Cap.pinValue G j e) (O.originalValue G) :=
  I.source (Cap.original G) j e (Cap.original_eo G j he) (Cap.presentation G)
    (nonzero G j e _ hc.1) (nonzero G j e _ hc.2.1)
    ((finite_iff_no_resonance G j e hc.2.1).mp hc.2.2)

def Applicable : Prop := ∃c : Cap.Choice s a,
  Signature.CentralSupport (G c.1) ∧ Coefficients G c.1 c.2

def selected (h : Applicable G) : Cap.Choice s a := Classical.choose h

theorem selected_spec (h : Applicable G) :
    Signature.CentralSupport (G (selected G h).1) ∧
      Coefficients G (selected G h).1 (selected G h).2 := Classical.choose_spec h

def selectedSource (h : Applicable G) := source G (selected G h).1 (selected G h).2
  (selected_spec G h).1 (selected_spec G h).2

/-- The previously accepted unequal-norm region is contained in the new test. -/
theorem of_unequal_norms (h : GeneralEOOriginalCapSource.Coefficients G j e) :
    Coefficients G j e := by
  refine ⟨h.1,h.2.1,?_⟩
  apply (finite_iff_no_resonance G j e h.2.1).mpr
  exact GeneralGeometricCapLocal.infinite_of_unequal_norms _ _
    (GeneralEOOriginalCapSource.second_nonzero G j e h)
    (GeneralEOOriginalCapSource.unequal G j e h)

/-- Every eligible cap rejected by this branch has a positive resonance at
the one fixed exponent. Rejection is not a tractability or ARS certificate. -/
theorem rejected_iff_resonant : ¬Applicable G ↔
    ∀c : Cap.Choice s a, Signature.CentralSupport (G c.1) →
      Cap.coefficient G c.1 c.2 ![false,true]≠0 →
      Cap.coefficient G c.1 c.2 ![true,false]≠0 →
      (I.p (Cap.original G) c.1 c.2/I.q (Cap.original G) c.1 c.2)^exponent G=1 := by
  classical
  constructor
  · intro h c he hp hq
    by_contra hr
    apply h
    refine ⟨c,he,hp,hq,?_⟩
    apply (finite_iff_no_resonance G c.1 c.2 hq).mpr
    exact (FiniteCapLocal.finite_iff_no_resonance _).mp hr
  · intro h ⟨c,he,hp,hq,hr⟩
    exact (finite_iff_no_resonance G c.1 c.2 hq).mp hr (exponent G) (exponent_pos G) (h c he hp hq)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEONonARSPinningFiniteCap
