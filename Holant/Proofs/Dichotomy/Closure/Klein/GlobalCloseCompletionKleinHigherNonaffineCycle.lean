import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinHigherNonaffineCounting

/-! Exact trace contractions and label support for alternating cycles of any
positive length. Orientation bits are retained for every M- and N-edge. -/
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffine
noncomputable section
open scoped BigOperators

def oriented (reverse : Bool) (A : Mat) : Mat := if reverse then Kernel.transpose A else A

def matrixProduct : List Mat → Mat
  | [] => Signature.equality
  | A::As => Kernel.mul A (matrixProduct As)

theorem representedProduct : ∀ (n : ℕ) (labels : Fin n → Label) (matrices : Fin n → Mat),
    (∀ i, Represents (labels i) (matrices i)) →
      Represents (∑ i, labels i) (matrixProduct (List.ofFn matrices)) := by
  intro n
  induction n with
  | zero =>
    intro labels matrices h
    have he : E 0 = (Signature.equality : Mat) := by
      funext x y
      exact E_zero x y
    simpa only [List.ofFn_zero,Fin.sum_univ_zero,matrixProduct,he] using represents_E 0
  | succ n ih =>
    intro labels matrices h
    rw [List.ofFn_succ,matrixProduct,Fin.sum_univ_succ]
    exact (h 0).mul (ih (fun i => labels i.succ) (fun i => matrices i.succ) (fun i => h i.succ))

theorem oriented_dual_represents (reverse : Bool) (a : Label) :
    Represents (dualLabelMap reverse a) (oriented reverse (dual a)) := by
  cases reverse
  · exact represents_dual a
  · change Represents a (Kernel.transpose (dual a))
    simpa only [theta_theta] using (represents_dual a).transpose

theorem oriented_E_represents (reverse : Bool) (a : Label) :
    Represents (directLabelMap reverse a) (oriented reverse (E a)) := by
  cases reverse
  · exact represents_E a
  · exact (represents_E a).transpose

/-- One alternating M/N pair in its actual traversal orientation. -/
def cycleFactor (mReverse nReverse : Bool) (a b : Label) : Mat :=
  Kernel.mul (oriented mReverse (dual a)) (oriented nReverse (E b))

/-- A length2(n+1) alternating cycle, contracted by the actual matrix products
and closing bit sum. The common-edge case is n=0. -/
def cycleCoefficient (n : ℕ) (fixed : Fin (n+1) → Label)
    (mReverse nReverse : Fin (n+1) → Bool) (labels : Fin (n+1) → Label) : ℂ :=
  Kernel.trace (matrixProduct (List.ofFn (fun i => cycleFactor (mReverse i) (nReverse i) (labels i) (fixed i))))

theorem cycleCoefficient_ne_zero_iff (n : ℕ) (fixed : Fin (n+1) → Label)
    (mReverse nReverse : Fin (n+1) → Bool) (labels : Fin (n+1) → Label) :
    cycleCoefficient n fixed mReverse nReverse labels ≠ 0 ↔
      (∑ i, dualLabelMap (mReverse i) (labels i)) = ∑ i, directLabelMap (nReverse i) (fixed i) := by
  have h := representedProduct (n+1)
    (fun i => dualLabelMap (mReverse i) (labels i)+directLabelMap (nReverse i) (fixed i))
    (fun i => cycleFactor (mReverse i) (nReverse i) (labels i) (fixed i))
    (fun i => (oriented_dual_represents (mReverse i) (labels i)).mul
      (oriented_E_represents (nReverse i) (fixed i)))
  have ht := h.trace_ne_zero_iff
  rw [Finset.sum_add_distrib,add_eq_zero_iff] at ht
  exact ht

/-- After any n original M-labels are chosen, exactly one final label works.
All successful coefficients are nonzero actual traces, with no cancellation
condition or support cardinality assumed. -/
theorem cycle_support_card (n : ℕ) (fixed : Fin (n+1) → Label)
    (mReverse nReverse : Fin (n+1) → Bool) :
    Fintype.card {labels : Fin (n+1) → Label // cycleCoefficient n fixed mReverse nReverse labels ≠ 0} = 4^n := by
  let e := Equiv.subtypeEquivRight (cycleCoefficient_ne_zero_iff n fixed mReverse nReverse)
  rw [Fintype.card_congr e]
  exact affineSolutions_card n (fun i => dualLabelMap (mReverse i))
    (∑ i, directLabelMap (nReverse i) (fixed i))

end
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffine
