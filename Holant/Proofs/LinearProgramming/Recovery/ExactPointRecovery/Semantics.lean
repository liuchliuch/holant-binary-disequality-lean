import Holant.Proofs.LinearProgramming.Support.MachineCombinators
import Holant.Proofs.LinearProgramming.Recovery.ExactPointRecovery.State

set_option autoImplicit false

/-! Kernel-checked recovery component. Ported into the exclusive task namespace and validated with the pinned toolchain.
The real request answers drive a bounded dyadic interval search. Existence
of a bounded-denominator coordinate minimum is derived from the original
LP, not supplied as an oracle. The final interval uniquely isolates that
scalar among denominator<=D rationals. This is not yet a scalar extractor
or a full vector recovery: no isolated rational is chosen as machine data.
-/
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.ExactPointRecovery
open Holant.LocalDrafts.TraversalCompletion.RationalLP
open Holant.LocalDrafts.RemoteWork.RationalLP.Foundation
open Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators
open Codec
namespace Semantics

def IsMinimum (c : CoordinateQuery) (t : ℚ) : Prop :=
  (∃ x, Feasible c.1.val x ∧ x c.2=t) ∧ ∀ y, Feasible c.1.val y → t≤y c.2

theorem request_bounds (c : CoordinateQuery) (k : ℕ) :
    0<(midpoint (payloadAt c k)).2.2 ∧
      (midpoint (payloadAt c k)).2.1≤(midpoint (payloadAt c k)).2.2 := by
  have hp := payloadAt_numerator c k
  have hq := payloadAt_denominator c k
  have hn : 0<2^k := by positivity
  dsimp [midpoint]
  rw [hq]
  omega

theorem midpoint_value (v : Payload) (hq : 0<denominator v) :
    ((midpoint v).2.1:ℚ)/(midpoint v).2.2=
      ((interval v).1+(interval v).2)/2 := by
  have hq' : (denominator v:ℚ)≠0 := by exact_mod_cast Nat.ne_of_gt hq
  dsimp [midpoint,interval]
  push_cast
  field_simp [hq'] <;> ring

theorem advance_interval (v : Payload) (hq : 0<denominator v) :
    interval (advance v)=
      if accepted v then ((interval v).1,((interval v).1+(interval v).2)/2)
      else (((interval v).1+(interval v).2)/2,(interval v).2) := by
  have hq' : (denominator v:ℚ)≠0 := by exact_mod_cast Nat.ne_of_gt hq
  cases ha : accepted v <;>
    simp only [advance,interval,numerator,denominator,ha,Bool.false_eq_true,↓reduceIte] <;>
    apply Prod.ext <;> push_cast <;> field_simp [hq'] <;> ring

theorem bracket (c : CoordinateQuery) (x : Fin c.1.val.dimension → ℚ)
    (hx : Feasible c.1.val x) (hm : ∀ y, Feasible c.1.val y → x c.2≤y c.2) (k : ℕ) :
    (interval (payloadAt c k)).1≤x c.2 ∧ x c.2≤(interval (payloadAt c k)).2 := by
  induction k with
  | zero => simpa [payloadAt,interval,numerator,denominator] using hx.2 c.2
  | succ k ih =>
    have hq : 0<denominator (payloadAt c k) := by rw [payloadAt_denominator]; positivity
    have hmid := midpoint_value (payloadAt c k) hq
    have hr := Request.accepted (coordinate (payloadAt c k))
      (midpoint (payloadAt c k)).2.1 (midpoint (payloadAt c k)).2.2
      (request_bounds c k).1
    change accepted (payloadAt c k)=true ↔
      ∃ y, Feasible (coordinate (payloadAt c k)).1.val y ∧
        y (coordinate (payloadAt c k)).2≤
          ((midpoint (payloadAt c k)).2.1:ℚ)/(midpoint (payloadAt c k)).2.2 at hr
    have hr' : accepted (payloadAt c k)=true ↔
        ∃ y, Feasible c.1.val y ∧ y c.2≤
          ((midpoint (payloadAt c k)).2.1:ℚ)/(midpoint (payloadAt c k)).2.2 := by
      exact Eq.mp (congrArg
        (fun q : CoordinateQuery => accepted (payloadAt c k)=true ↔
          ∃ y, Feasible q.1.val y ∧ y q.2≤
            ((midpoint (payloadAt c k)).2.1:ℚ)/(midpoint (payloadAt c k)).2.2)
        (payloadAt_coordinate c k)) hr
    rw [payloadAt,advance_interval _ hq]
    cases ha : accepted (payloadAt c k)
    · have hn : ¬∃ y, Feasible c.1.val y ∧ y c.2≤
          ((midpoint (payloadAt c k)).2.1:ℚ)/(midpoint (payloadAt c k)).2.2 := by
        intro he
        have ht := hr'.mpr he
        rw [ha] at ht
        contradiction
      have hnot : ¬x c.2≤((midpoint (payloadAt c k)).2.1:ℚ)/(midpoint (payloadAt c k)).2.2 :=
        fun h => hn ⟨x,hx,h⟩
      simp only [Bool.false_eq_true,↓reduceIte]
      exact ⟨by rw [← hmid]; exact (lt_of_not_ge hnot).le,ih.2⟩
    · obtain ⟨y,hy,hu⟩ := hr'.mp ha
      simp only [↓reduceIte]
      exact ⟨ih.1,by rw [← hmid]; exact (hm y hy).trans hu⟩

theorem width (c : CoordinateQuery) (k : ℕ) :
    (interval (payloadAt c k)).2-(interval (payloadAt c k)).1=(1:ℚ)/(2^k:ℕ) := by
  have hq : (2^k:ℚ)≠0 := by positivity
  simp only [interval,payloadAt_denominator]
  push_cast
  field_simp [hq] <;> ring

theorem terminal_isolates (c : CoordinateQuery) (h : ∃ x, Feasible c.1.val x) :
    ∃ t : ℚ, IsMinimum c t ∧ t.den≤InputBounds.denominator c.1.val ∧
      (interval (payload (resultState c))).1≤t ∧ t≤(interval (payload (resultState c))).2 ∧
      ∀ a : ℚ, a.den≤InputBounds.denominator c.1.val →
        (interval (payload (resultState c))).1≤a → a≤(interval (payload (resultState c))).2 → a=t := by
  obtain ⟨x,hx,hr,hm,hd⟩ := Denominator.minimum_bounded c.1.val c.2 h
  have hb := bracket c x hx hm (Denominator.rounds c.1.val)
  have hw : (interval (payload (resultState c))).2-(interval (payload (resultState c))).1<
      1/(InputBounds.denominator c.1.val:ℚ)^2 := by
    rw [result_exact]
    change (interval (payloadAt c (Denominator.rounds c.1.val))).2-
      (interval (payloadAt c (Denominator.rounds c.1.val))).1<_
    rw [width]
    exact Denominator.isolation_width c.1.val
  have hb' : (interval (payload (resultState c))).1≤x c.2 ∧
      x c.2≤(interval (payload (resultState c))).2 := by simpa [result_exact,payload,stamp] using hb
  refine ⟨x c.2,⟨⟨x,hx,rfl⟩,hm⟩,hd,hb'.1,hb'.2,?_⟩
  intro a ha hl hu
  exact Denominator.interval_unique _ (InputBounds.denominator_pos _) _ _ a (x c.2)
    ⟨hl,hu⟩ hb' ha hd hw

/-- The source query is preserved by every interval step. The subsequent
successive-face machine applies this interval procedure on the current
supporting face before each exact coordinate fixation. -/
theorem source_preserved (c : CoordinateQuery) : coordinate (payload (resultState c))=c := by
  simp [result_exact,payload,stamp]

end Semantics
end Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.ExactPointRecovery
