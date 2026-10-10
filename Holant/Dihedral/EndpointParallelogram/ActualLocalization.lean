import Holant.Dihedral.TwoCardLocalization.Interface

/-! The literal source6.12 endpoint test and its actual-card localization.

The four cosets below are precisely the local analytic data in the C/C
common-varying-edge branch. No equality of global matchings, physical endpoint
slices, localization program, or bounded-consumer conclusion is an input.
Physical inputs are the original two native-X cards and their full current-
group products. The phase-card identity and matching-involution bridge are
proved before invoking source6.6. Complete factor/deck-batch resolution is the
separate source6.7 statement and is not asserted here. -/
noncomputable section
namespace Holant.Dihedral.EndpointParallelogram
open Holant Holant.Marked Holant.Certificates
open Holant.Dihedral.CompatibleClosure Holant.Dihedral.TwoCardLocalization
set_option backward.isDefEq.respectTransparency false

theorem endpoint_phaseKernel_eq (b : Bool) (t : Scalar) :
    phaseKernel b t = M b t := by
  funext x y
  cases b <;> cases x <;> cases y <;> simp [phaseKernel,M,monomial]

/-- Exact contraction in the specified original ordered ports, including the
physical representative coefficient. -/
theorem card_eq_ordered_contract {n : ℕ} (q : Signature Scalar (n+2))
    (order : Equiv.Perm (Fin (n+2))) (b : Bool) (t c : Scalar) :
    card q order b t c = c • Signature.contract (M b t) (Tensor.reindex order.symm q) := by
  funext x
  simp only [card,endpoint_phaseKernel_eq,Signature.contract,Tensor.reindex,
    Pi.smul_apply,smul_eq_mul,Fintype.sum_bool]
  ring

/-- The physical native-X card is the analytic phase sum with its exact
original binary multiplier and actual realization scalar. -/
theorem native_card_eq_endpoint {m n : ℕ} {F : SignatureFamily Scalar}
    (G : ActualRepresentatives F m) (q : Signature Scalar (n+2))
    (order : Equiv.Perm (Fin (n+2))) (b : Bool)
    (t : {t : Scalar // Roots m t}) (c : Scalar) :
    c • nativeCardValue (Tensor.reindex order.symm q) (G.binary b t) =
      card q order b t.val (c * G.multiplier b t) := by
  rw [G.normalization,actual_close,smul_smul,card_eq_ordered_contract]
  rfl

/-- Matching equality means equality of the literal involutions on original
residual ports, independent of factor enumeration and edge orientation. -/
theorem pairing_eq_iff_presentation_mate {r s n : ℕ}
    (p : (Fin r × Bool) ≃ Fin n) (q : (Fin s × Bool) ≃ Fin n)
    (A : Fin r → Mat) (B : Fin s → Mat) (c d : Scalar) :
    Pairing.ofPorts p = Pairing.ofPorts q ↔
      (presentationMatching ⟨r,p,A,c⟩).mate = (presentationMatching ⟨s,q,B,d⟩).mate := by
  constructor
  · intro h
    apply Equiv.ext
    intro i
    exact congrArg (fun P : Pairing (Fin n) => P.mate i) h
  · intro h
    apply Pairing.ext
    funext i
    exact congrArg (fun P : Equiv.Perm (Fin n) => P i) h

/-- Only local support information from the stated C/C branch. These slices
are analytic functions of one original signature, never gadget resources. -/
structure EndpointCosets {n : ℕ} (q : Signature Scalar (n+2))
    (order : Equiv.Perm (Fin (n+2))) where
  direction : Submodule (ZMod 2) (Fin n → ZMod 2)
  a : Fin n → ZMod 2
  b : Fin n → ZMod 2
  c : Fin n → ZMod 2
  d : Fin n → ZMod 2
  support00 : fullCoset (slice q order false false) direction a
  support01 : fullCoset (slice q order false true) direction b
  support10 : fullCoset (slice q order true false) direction c
  support11 : fullCoset (slice q order true true) direction d
  even_displacement : a+d ∉ direction
  odd_displacement : b+c ∉ direction

/-- Actual source products, before building the typed source6.6 input.
All coefficients refer to the physical native-X contractions of the original
core in the supplied order. No alignment between the two products is assumed. -/
structure ActualProductCards {m n : ℕ} (k : ℕ) {F : SignatureFamily Scalar}
    (G : ActualRepresentatives F m) (q : Signature Scalar (n+2))
    (order : Equiv.Perm (Fin (n+2))) (t : Bool → {t : Scalar // Roots m t}) where
  ports : Bool → (Fin k × Bool) ≃ Fin n
  factors : Bool → Fin k → Mat
  factors_mem : ∀ b e,factors b e ∈ groupM m
  scalar : Bool → Scalar
  scalar_ne_zero : ∀ b,scalar b ≠ 0
  actualScalar : Bool → Scalar
  actualScalar_ne_zero : ∀ b,actualScalar b ≠ 0
  actual : ∀ b,Gadget.Realizes F .disequality
    (actualScalar b • nativeCardValue (Tensor.reindex order.symm q) (G.binary b (t b)))
  equation : ∀ b,actualScalar b • nativeCardValue (Tensor.reindex order.symm q) (G.binary b (t b)) =
    MatchingContractionClosure.productValue (ports b) (factors b) (scalar b)

namespace ActualProductCards
variable {m n k : ℕ} {F : SignatureFamily Scalar} {G : ActualRepresentatives F m}
  {q : Signature Scalar (n+2)} {order : Equiv.Perm (Fin (n+2))}
  {t : Bool → {t : Scalar // Roots m t}} (D : ActualProductCards k G q order t)

def coefficient (b : Bool) : Scalar := D.actualScalar b * G.multiplier b (t b)

theorem coefficient_ne_zero (b : Bool) : D.coefficient b ≠ 0 :=
  mul_ne_zero (D.actualScalar_ne_zero b) (G.multiplier_ne_zero b (t b))

theorem endpoint_equation (b : Bool) :
    card q order b (t b).val (D.coefficient b) =
      MatchingContractionClosure.productValue (D.ports b) (D.factors b) (D.scalar b) := by
  rw [coefficient,← native_card_eq_endpoint]
  exact D.equation b

theorem endpoint_actual (b : Bool) :
    Gadget.Realizes F .disequality (card q order b (t b).val (D.coefficient b)) := by
  rw [coefficient,← native_card_eq_endpoint]
  exact D.actual b

theorem endpoint_matching (hm : 0<m) (b : Bool) :
    ∃ offset,CardMatching (card q order b (t b).val (D.coefficient b))
      (Pairing.ofPorts (D.ports b)) offset := by
  rw [D.endpoint_equation]
  exact product_cardMatching (D.ports b) (D.factors b) (D.scalar b)
    (fun e => groupM_isMonomial hm (D.factors_mem b e)) (D.scalar_ne_zero b)

end ActualProductCards

/-- The source matching iff and actual nonzero-card conclusion, obtained from
the two original physical products rather than caller-supplied support witnesses. -/
theorem source_actual_product_endpoint_test {m n k : ℕ} (hm : 0<m)
    (F : SignatureFamily Scalar) (G : ActualRepresentatives F m)
    (q : Signature Scalar (n+2)) (order : Equiv.Perm (Fin (n+2)))
    (t : Bool → {t : Scalar // Roots m t}) (E : EndpointCosets q order)
    (D : ActualProductCards k G q order t) :
    (Pairing.ofPorts (D.ports false) = Pairing.ofPorts (D.ports true) ↔
      E.a+E.b+E.c+E.d ∈ E.direction) ∧
    card q order false (t false).val (D.coefficient false) ≠ 0 ∧
    card q order true (t true).val (D.coefficient true) ≠ 0 := by
  obtain ⟨e,he⟩ := D.endpoint_matching hm false
  obtain ⟨o,ho⟩ := D.endpoint_matching hm true
  have h := source_actual_card_endpoint_test F .disequality q order E.direction E.a E.b E.c E.d
    E.support00 E.support01 E.support10 E.support11 E.even_displacement E.odd_displacement
    (t false).val (t true).val (D.coefficient false) (D.coefficient true)
    ((t false).property.ne_zero hm) ((t true).property.ne_zero hm)
    (D.coefficient_ne_zero false) (D.coefficient_ne_zero true)
    (Pairing.ofPorts (D.ports false)) (Pairing.ofPorts (D.ports true)) e o he ho
    (D.endpoint_actual false) (D.endpoint_actual true)
  exact ⟨h.1,h.2.1,h.2.2.1⟩

/-- Construct the source6.6 data from the very same original actual cards. -/
def ActualProductCards.pairProducts {m r : ℕ} {F : SignatureFamily Scalar}
    {G : ActualRepresentatives F m} {q : Signature Scalar (2*r+6)}
    {order : Equiv.Perm (Fin (2*r+6))} {t : Bool → {t : Scalar // Roots m t}}
    (D : ActualProductCards (r+2) G q order t) :
    PairProducts G (fun b => (b,t b)) (Tensor.reindex order.symm q) where
  ports := D.ports
  factors := D.factors
  factors_mem := D.factors_mem
  scalar := D.scalar
  scalar_ne_zero := D.scalar_ne_zero
  actualScalar := D.actualScalar
  actualScalar_ne_zero := D.actualScalar_ne_zero
  actual := D.actual
  equation := D.equation

/-- Linearity of the recorded residual program, proved without modifying the
accepted localization dependencies. -/
theorem residual_program_smul {K I : Type*} [Field K] (C : I → Kernel K)
    {n l : ℕ} (P : Program I n l) (c : K) (f : Signature K n) :
    P.residual C (c • f) = c • P.residual C f := by
  induction P with
  | done n => rfl
  | step p i rest ih =>
    change rest.residual C (Signature.contract (C i)
      (c • Tensor.reindex p.symm f)) = c • rest.residual C _
    rw [contract_smul,ih]

/-- Every actual localized card is inherited from that same original native-X
card. The quotient records the original realization/binary multipliers and
the newly realized ancestor/card multipliers; none is silently discarded. -/
theorem localized_actual_from_original {m r : ℕ} {F : SignatureFamily Scalar}
    {G : ActualRepresentatives F m} {q : Signature Scalar (2*r+6)}
    {order : Equiv.Perm (Fin (2*r+6))} {t : Bool → {t : Scalar // Roots m t}}
    (D : ActualProductCards (r+2) G q order t)
    (R : LocalizationResult F (fun b => (b,t b)) (Tensor.reindex order.symm q)) (b : Bool) :
    R.cardScalar b • Signature.contract (M b (t b).val)
      (R.scalar • R.program.core TwoCardLocalization.phaseKernel (Tensor.reindex order.symm q)) =
    (R.cardScalar b * R.scalar / D.coefficient b) • R.program.residual TwoCardLocalization.phaseKernel
      (D.actualScalar b • nativeCardValue (Tensor.reindex order.symm q) (G.binary b (t b))) := by
  rw [native_card_eq_endpoint,card_eq_ordered_contract,residual_program_smul]
  have hi := R.inherited b
  change Signature.contract (M b (t b).val)
    (R.scalar • R.program.core TwoCardLocalization.phaseKernel (Tensor.reindex order.symm q)) =
      R.scalar • R.program.residual TwoCardLocalization.phaseKernel
        (Signature.contract (M b (t b).val) (Tensor.reindex order.symm q)) at hi
  rw [hi,smul_smul,smul_smul]
  apply congrArg (fun c : Scalar => c • R.program.residual TwoCardLocalization.phaseKernel
    (Signature.contract (M b (t b).val) (Tensor.reindex order.symm q)))
  exact (div_mul_cancel₀ _ (D.coefficient_ne_zero b)).symm

theorem localized_inheritance_scalar_ne_zero {m r : ℕ} {F : SignatureFamily Scalar}
    {G : ActualRepresentatives F m} {q : Signature Scalar (2*r+6)}
    {order : Equiv.Perm (Fin (2*r+6))} {t : Bool → {t : Scalar // Roots m t}}
    (D : ActualProductCards (r+2) G q order t)
    (R : LocalizationResult F (fun b => (b,t b)) (Tensor.reindex order.symm q)) (b : Bool) :
    R.cardScalar b * R.scalar / D.coefficient b ≠ 0 :=
  div_ne_zero (mul_ne_zero (R.cardScalar_ne_zero b) R.scalar_ne_zero) (D.coefficient_ne_zero b)

/-- Literal source6.12, including localization of failure through source6.6.
The output retains one actual six-port ancestor, the original ordered deleted
pair, inherited actual nonzero disagreement, exactly r representative uses,
and exclusion of a three-factor current-group product. No source6.7 resolution
or unproved external hardness result occurs in this theorem. -/
theorem source_actual_card_endpoint_localization {m r : ℕ} (hm : 3≤m)
    (F : SignatureFamily Scalar) (G : TransferRepresentatives F m)
    (q : Signature Scalar (2*r+6)) (hq : Gadget.Realizes F .disequality q)
    (order : Equiv.Perm (Fin (2*r+6))) (t : Bool → {t : Scalar // Roots m t})
    (E : EndpointCosets q order)
    (D : ActualProductCards (r+2) (G.connections (by omega)) q order t) :
    (Pairing.ofPorts (D.ports false) = Pairing.ofPorts (D.ports true) ↔
      E.a+E.b+E.c+E.d ∈ E.direction) ∧
    card q order false (t false).val (D.coefficient false) ≠ 0 ∧
    card q order true (t true).val (D.coefficient true) ≠ 0 ∧
    (E.a+E.b+E.c+E.d ∉ E.direction →
      D.pairProducts.Disagrees ∧
      Nonempty (LocalizationResult F (fun b => (b,t b)) (Tensor.reindex order.symm q))) := by
  have h := source_actual_product_endpoint_test (by omega) F (G.connections (by omega))
    q order t E D
  refine ⟨h.1,h.2.1,h.2.2,?_⟩
  intro hfail
  have hmatch : Pairing.ofPorts (D.ports false) ≠ Pairing.ofPorts (D.ports true) :=
    fun he => hfail (h.1.mp he)
  have hd : D.pairProducts.Disagrees := by
    left
    intro he
    exact hmatch (Pairing.ext he)
  exact ⟨hd,source_two_card_localization_ordered hm F G r q hq order
    (fun b => (b,t b)) D.pairProducts hd⟩

end Holant.Dihedral.EndpointParallelogram
