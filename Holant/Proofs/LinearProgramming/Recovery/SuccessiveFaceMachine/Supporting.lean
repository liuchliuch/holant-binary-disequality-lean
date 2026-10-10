import Holant.Proofs.LinearProgramming.Support.MachineCombinators
import Holant.Proofs.LinearProgramming.Recovery.SuccessiveFaceMachine.ScalarProgram

set_option autoImplicit false

/-! Kernel-checked recovery component. Supporting minimum faces inherit ORIGINAL rigid points.
The mathematical minima below are produced by old Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve.Completion.Minimum.exists_minimum
and the actual scalar recovery theorem; they are never machine input fields.
Both boundary motions are existence proofs used only to eliminate a tangent.
-/
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.SuccessiveFaceMachine
open Holant.LocalDrafts.TraversalCompletion.RationalLP
open Holant.LocalDrafts.RemoteWork.RationalLP.Foundation
open Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators
open Codec Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve.FaceMove
open scoped BigOperators

theorem minimum_tangent_zero (d : Raw) (j : Fin d.dimension) (x v : Fin d.dimension → ℚ)
    (hx : Feasible d x) (hm : ∀ y, Feasible d y → x j≤y j) (hv : Tangent d x v) : v j=0 := by
  by_cases hz : v=0
  · simp [hz]
  · obtain ⟨t,k,ht,hk,hy,_,_,_⟩ := first_boundary d x v hx hv hz
    have hvn := Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve.Completion.Minimum.tangent_neg d x v hv
    obtain ⟨s,l,hs,hl,hyneg,_,_,_⟩ := first_boundary d x (-v) hx hvn (neg_ne_zero.mpr hz)
    have hp := hm _ hy
    have hn := hm _ hyneg
    have htp : 0≤t*v j := by dsimp [move] at hp; linarith
    have hsn : s*v j≤0 := by dsimp [move] at hn; simp only [Pi.neg_apply,mul_neg] at hn; linarith
    have hpos : 0≤v j := nonneg_of_mul_nonneg_right htp ht
    have hneg : v j≤0 := nonpos_of_mul_nonpos_right hsn hs
    exact le_antisymm hneg hpos

theorem fixed_tangent (d : Raw) (j : Fin d.dimension) (p q : ℕ) (x v : Fin d.dimension → ℚ)
    (hv : Tangent d x v) (hj : v j=0) : Tangent (ExactPointRecovery.Threshold.fixedValue d j p q).val x v := by
  refine ⟨?_,hv.2⟩
  intro i
  have he (k : Fin d.dimension) :
      (ExactPointRecovery.Threshold.fixedValue d j p q).val.coefficient i k =
        ExactPointRecovery.Threshold.fixedCoefficients d j q i k :=
    Codec.pack_coefficient (d.rowCount+1) d.dimension
      (ExactPointRecovery.Threshold.fixedCoefficients d j q)
      (ExactPointRecovery.Threshold.constants d p) i k
  change (∑ k : Fin d.dimension,
    ((ExactPointRecovery.Threshold.fixedValue d j p q).val.coefficient i k : ℚ)*v k)=0
  have hs : (∑ k : Fin d.dimension,
      ((ExactPointRecovery.Threshold.fixedValue d j p q).val.coefficient i k : ℚ)*v k)=
      ∑ k : Fin d.dimension, (ExactPointRecovery.Threshold.fixedCoefficients d j q i k : ℚ)*v k := by
    apply Finset.sum_congr rfl
    intro k _
    rw [he k]
  rw [hs]
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simp [ExactPointRecovery.Threshold.fixedCoefficients,hj]
  · simpa only [ExactPointRecovery.Threshold.fixedCoefficients,Fin.lastCases_castSucc] using hv.1 i

theorem supporting_rigid (d : Raw) (j : Fin d.dimension) (p q : ℕ) (hq : 0<q)
    (hm : ∀ y, Feasible d y → (p:ℚ)/q≤y j) (x : Fin d.dimension → ℚ)
    (hx : Feasible (ExactPointRecovery.Threshold.fixedValue d j p q).val x)
    (hr : Rigid (ExactPointRecovery.Threshold.fixedValue d j p q).val x) : Rigid d x := by
  have hf := (ExactPointRecovery.Threshold.fixed_feasible d j p q hq x).mp hx
  intro v hv
  have hj := minimum_tangent_zero d j x v hf.1 (by intro y hy; rw [hf.2]; exact hm y hy) hv
  exact hr v (fixed_tangent d j p q x v hv hj)

/-- Inductive semantic invariant only, not an encoded Context field. -/
def Supporting (c : Context) : Prop :=
  (∀ x, Feasible c.current.1.val x → Feasible c.original.val (project c x)) ∧
  (∀ x, Feasible c.current.1.val x → Rigid c.current.1.val x → Rigid c.original.val (project c x))
theorem initial_supporting (d : Codec.Input) (j : Fin d.val.dimension) : Supporting (Context.initial d j) := by
  constructor
  · intro x hx; change Feasible d.val x; exact hx
  · intro x hx hr; change Rigid d.val x; exact hr

theorem positive_ratio (r : ℚ) (hr : 0≤r) : (r.num.toNat:ℚ)/r.den=r := by
  have hn := Rat.num_nonneg.mpr hr
  have hi : (r.num.toNat:ℤ)=r.num := Int.toNat_of_nonneg hn
  have he : (r.num.toNat:ℚ)=(r.num:ℚ) := by exact_mod_cast hi
  rw [he,Rat.num_div_den]
theorem fix_feasible (c : Context) (r : ℚ) (hr : 0≤r) (x : Fin c.current.1.val.dimension → ℚ) :
    Feasible (Context.fix c r).current.1.val x ↔ Feasible c.current.1.val x ∧ x c.current.2=r := by
  have hf := ExactPointRecovery.ThresholdProgram.fixed_feasible c.current r.num.toNat r.den r.den_pos x
  simpa only [Context.fix,positive_ratio r hr] using hf

/-- Transport the tangent through the actual appended integer row. Only
the rows projection of the physical compiler's exact equality is used;
the original dimension, x and v remain the same typed functions. -/
theorem fix_tangent (c : Context) (r : ℚ)
    (x v : Fin c.current.1.val.dimension → ℚ)
    (hv : Tangent c.current.1.val x v) (hj : v c.current.2=0) :
    Tangent (Context.fix c r).current.1.val x v := by
  have hm := fixed_tangent c.current.1.val c.current.2 r.num.toNat r.den x v hv hj
  have hrows := congrArg Raw.rows
    (ExactPointRecovery.ThresholdProgram.fixed_exact c.current.1 c.current.2 r.num.toNat r.den)
  have hc (i : Fin (c.current.1.val.rowCount+1)) (j : Fin c.current.1.val.dimension) :
      (Context.fix c r).current.1.val.coefficient i j=
        (ExactPointRecovery.Threshold.fixedValue c.current.1.val c.current.2 r.num.toNat r.den).val.coefficient i j := by
    change (ExactPointRecovery.ThresholdProgram.rawFixed
      (c.current.1.val,c.current.2.val,r.num.toNat,r.den)).coefficient i j=_
    unfold Raw.coefficient
    rw [hrows]
  refine ⟨?_,hm.2⟩
  intro i
  have he : (∑ k : Fin c.current.1.val.dimension,
      ((Context.fix c r).current.1.val.coefficient i k : ℚ)*v k)=
      ∑ k : Fin c.current.1.val.dimension,
        ((ExactPointRecovery.Threshold.fixedValue c.current.1.val c.current.2 r.num.toNat r.den).val.coefficient i k : ℚ)*v k := by
    apply Finset.sum_congr rfl
    intro k _
    rw [hc i k]
  exact he.trans (hm.1 i)

theorem fix_supporting (c : Context) (r : ℚ) (hr : 0≤r) (hc : Supporting c)
    (hm : ∀ y, Feasible c.current.1.val y → r≤y c.current.2) : Supporting (Context.fix c r) := by
  constructor
  · intro x hx
    have hf := (fix_feasible c r hr x).mp hx
    change Feasible c.original.val (project c x)
    exact hc.1 x hf.1
  · intro x hx hrigid
    have hf := (fix_feasible c r hr x).mp hx
    have hg : Rigid c.current.1.val x := by
      intro v hv
      have hj := minimum_tangent_zero c.current.1.val c.current.2 x v hf.1
        (by intro y hy; rw [hf.2]; exact hm y hy) hv
      exact hrigid v (fix_tangent c r x v hv hj)
    change Rigid c.original.val (project c x)
    exact hc.2 x hf.1 hg

theorem original_minimum (c : Context) (hs : Supporting c) (hn : ∃ x, Feasible c.current.1.val x) :
    ∃ x, Feasible c.current.1.val x ∧ Rigid c.current.1.val x ∧
      (∀ y, Feasible c.current.1.val y → x c.current.2≤y c.current.2) ∧
      (x c.current.2).den≤InputBounds.denominator c.original.val := by
  obtain ⟨x,hx,hr,hm⟩ := Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve.Completion.Minimum.exists_minimum c.current.1.val c.current.2 hn
  have ho := hs.1 x hx
  have hro := hs.2 x hx hr
  have hd := ExactPointRecovery.Denominator.rigid_denominator c.original.val (project c x) ho hro
    (Fin.cast c.sameDimension c.current.2)
  refine ⟨x,hx,hr,hm,?_⟩
  simpa [project] using hd

namespace Scalar
theorem recovers_minimum (c : Context) (hs : Supporting c) (hn : ∃ x, Feasible c.current.1.val x) :
    ∃ r, value c=Option.some r ∧ ExactPointRecovery.Semantics.IsMinimum c.current r ∧
      r.den≤InputBounds.denominator c.original.val := by
  obtain ⟨x,hx,hr,hm,hd⟩ := original_minimum c hs hn
  have hb := ExactPointRecovery.Semantics.bracket c.current x hx hm
    (ExactPointRecovery.Denominator.rounds c.current.1.val)
  have hi : lower c≤x c.current.2 ∧ x c.current.2≤upper c := by
    simpa [lower,upper,intervalPayload,ExactPointRecovery.result_exact,
      ExactPointRecovery.payload,ExactPointRecovery.stamp,ExactPointRecovery.interval] using hb
  have hc : RationalExtraction.Candidate (query c).val (x c.current.2) := ⟨hi.1,hi.2,hd⟩
  exact ⟨x c.current.2,RationalExtraction.Source.recovers (query c) _ hc,⟨⟨x,hx,rfl⟩,hm⟩,hd⟩
end Scalar
end Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.SuccessiveFaceMachine
