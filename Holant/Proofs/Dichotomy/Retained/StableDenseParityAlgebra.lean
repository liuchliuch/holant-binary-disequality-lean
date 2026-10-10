import Holant.Proofs.Hardness.EightVertexCapLocal

/-! Exact coefficient reduction for dense eight-vertex cancellation. The
corner values remain arbitrary and nonzero. A pair of optional EO entries
can vanish simultaneously only on one explicit quadratic locus. Cap weights
are the twelve actual original-M loops, never freely selected parameters. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableDenseParityAlgebra
open Holant Holant.LocalDrafts.Hardness.EightVertexNonexception
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
variable {K : Type} [Field K]

/-- All eight original coefficients, including both corners, are live. -/
def Dense (M : Signature K 4) : Prop :=
  (entries M).a ≠ 0 ∧ (entries M).b ≠ 0 ∧
  (entries M).c ≠ 0 ∧ (entries M).d ≠ 0 ∧
  (entries M).w ≠ 0 ∧ (entries M).z ≠ 0 ∧
  (entries M).y ≠ 0 ∧ (entries M).x ≠ 0

/-- The precise obstruction to getting a fifth EO coefficient once the
four mandatory coefficients survive. This is a literal original-table test. -/
def DoubleCancellation (M : Signature K 4) : Prop :=
  (entries M).d = (entries M).w ∧
    (entries M).c * (entries M).z + (entries M).d ^ 2 = 0

/-- Difference of the two optional coefficients factors into their sum and
opposite difference. No realness, unit modulus, or genericity is assumed. -/
theorem optional_zeros_iff (M : Signature K 4)
    (hs : (entries M).w + (entries M).d ≠ 0) :
    ((entries M).c * (entries M).z + (entries M).d ^ 2 = 0 ∧
     (entries M).c * (entries M).z + (entries M).w ^ 2 = 0) ↔
      DoubleCancellation M := by
  constructor
  · rintro ⟨hd,hw⟩
    have product : ((entries M).d - (entries M).w) *
        ((entries M).w + (entries M).d) = 0 := by linear_combination hd - hw
    exact ⟨sub_eq_zero.mp ((mul_eq_zero.mp product).resolve_right hs),hd⟩
  · rintro ⟨same,zero⟩
    exact ⟨zero,by rwa [← same]⟩

/-- Exactly four coefficient tests remain on a dense even original table. -/
structure Region (M : Signature K 4) : Prop where
  cancel : (entries M).b + (entries M).y = 0
  outer : (entries M).a * (entries M).x + (entries M).b ^ 2 ≠ 0
  sum : (entries M).w + (entries M).d ≠ 0
  exceptional : ¬ DoubleCancellation M

theorem applicable_iff (M : Signature K 4) (he : EvenSupport M) (hd : Dense M) :
    EightVertexCancellationLocal.Applicable M ↔ Region M := by
  constructor
  · intro h
    refine ⟨h.cancel,h.outer,h.sum,?_⟩
    intro exceptional
    have both := (optional_zeros_iff M h.sum).mpr exceptional
    exact h.additional.elim (fun h => h both.1) (fun h => h both.2)
  · intro h
    refine ⟨he,h.cancel,h.outer,hd.2.2.1,hd.2.2.2.2.2.1,h.sum,?_⟩
    classical
    by_contra absent
    push Not at absent
    exact h.exceptional ((optional_zeros_iff M h.sum).mp absent)

/-- A convenient strict subregion needs only one separation inequality.
It supplies both the nonzero mandatory sum and the optional fifth entry. -/
theorem region_of_square_separation (M : Signature K 4)
    (hc : (entries M).b + (entries M).y = 0)
    (ho : (entries M).a * (entries M).x + (entries M).b ^ 2 ≠ 0)
    (hs : (entries M).d ^ 2 ≠ (entries M).w ^ 2) : Region M := by
  refine ⟨hc,ho,?_,?_⟩
  · intro zero
    apply hs
    have hw : (entries M).w = -(entries M).d := by linear_combination zero
    rw [hw]
    ring
  · intro bad
    exact hs (congrArg (fun x : K => x ^ 2) bad.1)

/-- All weights here are supplied by an actual original-M cap. -/
structure CapRegion (M : Signature K 4) (k : GeneralCancellationCapPin.Choice) : Prop where
  cancel : EightVertexCapLocal.p M k * (entries M).b +
    EightVertexCapLocal.q M k * (entries M).y = 0
  outer : (EightVertexCapLocal.p M k * (entries M).a) *
    (EightVertexCapLocal.q M k * (entries M).x) +
      (EightVertexCapLocal.p M k * (entries M).b) ^ 2 ≠ 0
  sum : EightVertexCapLocal.q M k * (entries M).w +
    EightVertexCapLocal.p M k * (entries M).d ≠ 0
  exceptional : ¬ (EightVertexCapLocal.p M k * (entries M).d =
      EightVertexCapLocal.q M k * (entries M).w ∧
    (EightVertexCapLocal.p M k * (entries M).c) *
      (EightVertexCapLocal.q M k * (entries M).z) +
        (EightVertexCapLocal.p M k * (entries M).d) ^ 2 = 0)

/-- Outer survival and cancellation force BOTH physical cap weights to be
nonzero. No independent cap-nonsingularity hypothesis is supplied. -/
theorem cap_weights_nonzero (M : Signature K 4) (hd : Dense M)
    (k : GeneralCancellationCapPin.Choice) (h : CapRegion M k) :
    EightVertexCapLocal.p M k ≠ 0 ∧ EightVertexCapLocal.q M k ≠ 0 := by
  have hp : EightVertexCapLocal.p M k ≠ 0 := by
    intro zero
    exact h.outer (by simp [zero])
  refine ⟨hp,?_⟩
  intro zero
  have cancel := h.cancel
  simp only [zero,zero_mul,add_zero] at cancel
  exact (mul_ne_zero hp hd.2.1) cancel

/-- The original dense table supplies the two missing nonzero hypotheses;
the quadratic obstruction supplies the optional surviving EO entry. -/
theorem cap_coefficients (M : Signature K 4) (hd : Dense M)
    (k : GeneralCancellationCapPin.Choice) (h : CapRegion M k) :
    EightVertexCapLocal.Coefficients M k := by
  have hn := cap_weights_nonzero M hd k h
  refine ⟨h.cancel,h.outer,mul_ne_zero hn.1 hd.2.2.1,
    mul_ne_zero hn.2 hd.2.2.2.2.2.1,h.sum,?_⟩
  have hs : (entries (EightVertexCapLocal.output M k)).w +
      (entries (EightVertexCapLocal.output M k)).d ≠ 0 := h.sum
  have he : ¬ DoubleCancellation (EightVertexCapLocal.output M k) := h.exceptional
  classical
  by_contra absent
  push Not at absent
  exact he ((optional_zeros_iff (EightVertexCapLocal.output M k) hs).mp absent)

theorem cap_applicable (M : Signature K 4) (he : EvenSupport M) (hd : Dense M)
    (k : GeneralCancellationCapPin.Choice) (h : CapRegion M k) :
    EightVertexCapLocal.Applicable M := ⟨he,k,cap_coefficients M hd k h⟩

/-- A failed accepted cancellation test has a precise algebraic explanation,
provided its corner cancellation equation holds. -/
theorem cancellation_residual (M : Signature K 4) (he : EvenSupport M) (hd : Dense M)
    (hc : (entries M).b + (entries M).y = 0)
    (hn : ¬ EightVertexCancellationLocal.Applicable M) :
    (entries M).a * (entries M).x + (entries M).b ^ 2 = 0 ∨
      (entries M).w + (entries M).d = 0 ∨ DoubleCancellation M := by
  classical
  by_contra missing
  push Not at missing
  exact hn ((applicable_iff M he hd).mpr ⟨hc,missing.1,missing.2.1,missing.2.2⟩)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableDenseParityAlgebra
end
