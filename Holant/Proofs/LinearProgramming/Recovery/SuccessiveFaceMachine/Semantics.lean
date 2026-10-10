import Holant.Proofs.LinearProgramming.Support.MachineCombinators
import Holant.Proofs.LinearProgramming.Recovery.SuccessiveFaceMachine.Body

set_option autoImplicit false

/-! Kernel-checked recovery component. Every restored coordinate is fixed on the SAME current
nonempty supporting face. The witness below proves output meaning only; its
bytes are never initial data or a selected machine operation. The actual
scalar Option supplies every appended list entry and fixed equality row.
-/
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.SuccessiveFaceMachine
open Holant.LocalDrafts.TraversalCompletion.RationalLP
open Holant.LocalDrafts.RemoteWork.RationalLP.Foundation
open Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators
namespace Semantics
open Codec

@[simp] theorem next_original (c : Context) (r : ℚ) : (c.next r).original=c.original := rfl
@[simp] theorem next_project (c : Context) (r : ℚ)
    (x : Fin c.current.1.val.dimension → ℚ) : project (c.next r) x=project c x := rfl
theorem advanced_original (p : Payload) : (context (advance p)).original=(context p).original := by
  unfold advance cell update
  split
  · split <;> rfl
  · rfl
@[simp] theorem original_at (d : Input) (k : ℕ) : (context («at» d k)).original=d.val := by
  induction k with
  | zero => rfl
  | succ k ih => exact (advanced_original («at» d k)).trans ih
theorem failed_at (d : Input) (h : alive (initialPayload d)=false) (k : ℕ) : «at» d k=initialPayload d := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [«at»,ih] using advance_failed (initialPayload d) h
theorem unavailable (d : Input) (hn : ¬∃ x, Feasible d.val.val x) : value d=none := by
  have hf : alive (initialPayload d)=false := (Holant.LocalDrafts.RemoteWork.RationalLP.Complexity.CounterLoop.Receipt.rejected d).mpr hn
  rw [value,result_exact,failed_at d hf]
  simp [hf]

/-- Proof invariant of actual execution, never an encoded program field. -/
def Good (k : ℕ) (p : Payload) : Prop :=
  alive p=true ∧ Supporting (context p) ∧
  (∃ x, Feasible (context p).current.1.val x) ∧
  (points p).length=k ∧
  (k<(context p).original.val.dimension → (context p).current.2.val=k) ∧
  ∀ x, Feasible (context p).current.1.val x →
    ∀ j : Fin (context p).original.val.dimension, j.val<k →
      project (context p) x j=(points p).getD j.val 0

theorem initial_good (d : Input) (hn : ∃ x, Feasible d.val.val x) : Good 0 (initialPayload d) := by
  refine ⟨(Holant.LocalDrafts.RemoteWork.RationalLP.Complexity.CounterLoop.Receipt.accepted d).mpr hn,initial_supporting d.val _,hn,rfl,?_,?_⟩
  · intro h; rfl
  · intro x hx j hj; omega

theorem good_advance (k : ℕ) (p : Payload) (hp : Good k p)
    (hk : k<(context p).original.val.dimension) : Good (k+1) (advance p) := by
  rcases hp with ⟨ha,hs,hn,hl,hj,hprefix⟩
  obtain ⟨r,he,⟨⟨x,hx,hxr⟩,hm⟩,hd⟩ := Scalar.recovers_minimum (context p) hs hn
  have hb := Scalar.returned_bounds (context p) r he
  have hv : advance p=((context p).next r,points p++[r],true) := by
    simp [advance,cell,update,ha,he]
  rw [hv]
  refine ⟨rfl,next_supporting (context p) r hb.1 hs hm,
    ⟨x,(next_feasible (context p) r hb.1 x).mpr ⟨hx,hxr⟩⟩,
    by simpa [points,List.length_append,hl],?_,?_⟩
  · intro hnext
    change k+1<(context p).original.val.dimension at hnext
    have hport := hj hk
    have hdimen := (context p).sameDimension
    have hnot : (context p).current.2.val+1≠(context p).current.1.val.dimension := by omega
    change (successorIndex ((context p).fix r).current).val=k+1
    rw [successorIndex_value]
    change (if (context p).current.2.val+1=(context p).current.1.val.dimension then 0
      else (context p).current.2.val+1)=k+1
    rw [if_neg hnot,hport]
  · intro y hy j hjnext
    have hyold := (next_feasible (context p) r hb.1 y).mp hy
    by_cases hjold : j.val<k
    · have hprev := hprefix y hyold.1 j hjold
      have hget : (points p++[r]).getD j.val 0=(points p).getD j.val 0 :=
        List.getD_append (points p) [r] 0 j.val (by rw [hl]; exact hjold)
      change project (context p) y j=(points p++[r]).getD j.val 0
      rw [hget]
      exact hprev
    · have hjval : j.val=k := by omega
      have hcast : Fin.cast (context p).sameDimension.symm j=(context p).current.2 := by
        apply Fin.ext
        change j.val=(context p).current.2.val
        exact hjval.trans (hj hk).symm
      change project (context p) y j=(points p++[r]).getD j.val 0
      have hget : (points p++[r]).getD j.val 0=r := by
        rw [List.getD_append_right (points p) [r] 0 j.val (by rw [hl]; omega)]
        simp [hl,hjval]
      rw [hget]
      simpa only [project,hcast] using hyold.2

theorem at_good (d : Input) (hn : ∃ x, Feasible d.val.val x) (k : ℕ)
    (hk : k≤d.val.val.dimension) : Good k («at» d k) := by
  induction k with
  | zero => exact initial_good d hn
  | succ k ih =>
    exact good_advance k («at» d k) (ih (by omega)) (by rw [original_at]; omega)

theorem common_solution (d : Input) (hn : ∃ x, Feasible d.val.val x) :
    Codec.Solution d.val.val (points («at» d d.val.val.dimension)) := by
  let p := «at» d d.val.val.dimension
  obtain ⟨ha,hs,⟨x,hx⟩,hl,hj,hprefix⟩ := at_good d hn d.val.val.dimension le_rfl
  have ho : (context p).original=d.val := original_at d d.val.val.dimension
  have hv : Codec.point (context p).original.val (points p)=project (context p) x := by
    funext j
    exact (hprefix x hx j (by simpa only [ho] using j.isLt)).symm
  have sol : Codec.Solution (context p).original.val (points p) :=
    ⟨by simpa only [ho] using hl,by rw [hv]; exact hs.1 x hx⟩
  simpa only [ho] using sol

theorem available (d : Input) (hn : ∃ x, Feasible d.val.val x) :
    value d=some (points («at» d d.val.val.dimension)) := by
  have ha := (at_good d hn d.val.val.dimension le_rfl).1
  simp only [value,result_exact,ha,↓reduceIte]

theorem response (d : Input) : Codec.Response d.val.val (value d) := by
  classical
  by_cases hn : ∃ x, Feasible d.val.val x
  · rw [available d hn]
    exact common_solution d hn
  · rw [unavailable d hn]
    exact hn
theorem some_sound (d : Input) (xs : List ℚ) (he : value d=some xs) : Codec.Solution d.val.val xs := by
  simpa only [he,Codec.Response] using response d
theorem none_iff (d : Input) : value d=none ↔ ¬∃ x, Feasible d.val.val x := by
  constructor
  · intro he; simpa only [he,Codec.Response] using response d
  · exact unavailable d
end Semantics
end Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.SuccessiveFaceMachine
