import Holant.Proofs.LinearProgramming.Optimization.Search.Containment

/-!
Actual trajectory from the original Raw input. Its containment and nonsingular
factor invariants are proved by induction from start, not supplied by callers.
Terminal states stay fixed. Fuel is only an observation index here: no claim
that an arbitrary timeout decides infeasibility, and no FP capstone.
-/
open Holant.LocalDrafts.TraversalCompletion.RationalLP
open Holant.LocalDrafts.RemoteWork.RationalLP.Foundation Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve.Completion

namespace Holant.LocalDrafts.RemoteWork.RationalLP.Optimization.Search.Trajectory
open FactorUpdate Containment
noncomputable section

def step (d : Codec.Raw) (s : State d.dimension) : State d.dimension :=
  match Separation.separate d s.center with
  | none => s
  | some c => if Separation.normal d c=0 then s else update s (Separation.normal d c)

def run (d : Codec.Raw) (k : ℕ) : State d.dimension := ((step d)^[k]) (start d.dimension)

theorem invariant (d : Codec.Raw) (hn : 2≤d.dimension) (k : ℕ) :
    (run d k).factor.det≠0 ∧
    ∀ x, Thickening.At d (Thickening.epsilon d) x → Contains (run d k) x := by
  induction k with
  | zero => exact ⟨start_nonsingular _,start_contains d⟩
  | succ k ih =>
    have hr : run d (k+1)=step d (run d k) := Function.iterate_succ_apply' _ _ _
    rw [hr]
    cases hc : Separation.separate d (run d k).center with
    | none => simpa only [step,hc] using ih
    | some c =>
      by_cases hg : Separation.normal d c=0
      · simpa only [step,hc,if_pos hg] using ih
      · simp only [step,hc,if_neg hg]
        exact ⟨(actual_cut_progress d hn _ c ih.1 hg).1,
          actual_cut_contains d hn _ c ih.1 hc hg ih.2⟩

theorem active_progress (d : Codec.Raw) (hn : 2≤d.dimension) (k : ℕ)
    (c : Separation.Constraint d) (hc : Separation.separate d (run d k).center=some c)
    (hg : Separation.normal d c≠0) :
    |(run d (k+1)).factor.det|≤|(run d k).factor.det| * Scales.contraction d.dimension := by
  have hr : run d (k+1)=step d (run d k) := Function.iterate_succ_apply' _ _ _
  rw [hr]
  simp only [step,hc,if_neg hg]
  exact (actual_cut_progress d hn _ c (invariant d hn k).1 hg).2

theorem accepted (d : Codec.Raw) (k : ℕ)
    (h : Separation.separate d (run d k).center=none) : ∃ x, Codec.Feasible d x :=
  (Thickening.nonempty_iff d).mp ⟨_,(Separation.none_iff d _).mp h⟩

theorem rejected_zero (d : Codec.Raw) (k : ℕ) (c : Separation.Constraint d)
    (hc : Separation.separate d (run d k).center=some c) (hg : Separation.normal d c=0) :
    ¬∃ x, Codec.Feasible d x := Separation.zero_cut_reject d _ c hc hg

theorem accepted_fixed (d : Codec.Raw) (k t : ℕ)
    (h : Separation.separate d (run d k).center=none) : run d (k+t)=run d k := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hr : run d (k+(t+1))=step d (run d (k+t)) := by
      simpa only [run,Nat.succ_eq_add_one,Nat.add_assoc] using
        (Function.iterate_succ_apply' (step d) (k+t) (start d.dimension))
    rw [hr,ih]
    simp only [step,h]

end
end Holant.LocalDrafts.RemoteWork.RationalLP.Optimization.Search.Trajectory
