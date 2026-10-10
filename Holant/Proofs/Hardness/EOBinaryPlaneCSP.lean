import Holant.Proofs.Hardness.EOBinaryPlaneCycles
import Mathlib.Logic.Equiv.Fin.Rotate

/-! Every ordinary finite binary CSP with no unused variables has an internally
constructed occurrence-cycle presentation. This establishes the exact semantic
bridge, including loops, repeated constraints, and the empty instance. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneCSP
open Holant
open scoped BigOperators
namespace C
export EOBinaryPlaneCycles (Slot incidence Consistent weight value network denote_lift)
end C
set_option backward.isDefEq.respectTransparency false

private theorem rotation_constant {d : ℕ} (a : Fin d→Bool)
    (h : ∀i,a (finRotate d i)=a i) (i j : Fin d) : a i=a j := by
  cases d with
  | zero => exact Fin.elim0 i
  | succ d =>
    have hz (k : Fin (d+1)) : a k=a 0 := by
      induction k using Fin.induction with
      | zero => rfl
      | succ k ih =>
        have hk := h k.castSucc
        have hr : finRotate (d+1) k.castSucc=k.succ := finRotate_of_lt k.isLt
        rw [hr] at hk
        exact hk.trans ih
    exact (hz i).trans (hz j).symm

abbrev Fiber {n m : ℕ} (scope : C.Slot n→Fin m) (v : Fin m) := {s // scope s=v}

def fiberNext {n m : ℕ} (scope : C.Slot n→Fin m) (v : Fin m) : Equiv.Perm (Fiber scope v) :=
  (Fintype.equivFin (Fiber scope v)).trans
    ((finRotate (Fintype.card (Fiber scope v))).trans (Fintype.equivFin (Fiber scope v)).symm)

def next {n m : ℕ} (scope : C.Slot n→Fin m) : Equiv.Perm (C.Slot n) :=
  Equiv.ofFiberEquiv (fiberNext scope)

theorem scope_next {n m : ℕ} (scope : C.Slot n→Fin m) (s : C.Slot n) :
    scope (next scope s)=scope s := Equiv.ofFiberEquiv_map _ _

theorem next_fiber {n m : ℕ} (scope : C.Slot n→Fin m) (v : Fin m) (s : Fiber scope v) :
    next scope s.val=(fiberNext scope v s).val := by
  rcases s with ⟨s,hs⟩
  subst v
  rfl

theorem consistent_fiber {n m : ℕ} (scope : C.Slot n→Fin m) (a : C.Slot n→Bool)
    (h : C.Consistent (next scope) a) (s t : C.Slot n) (hst : scope s=scope t) : a s=a t := by
  let E := Fintype.equivFin (Fiber scope (scope s))
  let b : Fin (Fintype.card (Fiber scope (scope s)))→Bool := fun i=>a (E.symm i).val
  have hb (i : Fin (Fintype.card (Fiber scope (scope s)))) : b (finRotate _ i)=b i := by
    have hi := h (E.symm i).val
    rw [next_fiber scope (scope s)] at hi
    simpa only [b,fiberNext,Equiv.trans_apply,Equiv.apply_symm_apply,E] using hi
  have hi := rotation_constant b hb (E ⟨s,rfl⟩) (E ⟨t,hst.symm⟩)
  simpa only [b,Equiv.symm_apply_apply] using hi

def representative {n m : ℕ} (scope : C.Slot n→Fin m) (hs : Function.Surjective scope)
    (v : Fin m) : C.Slot n := (hs v).choose

theorem representative_scope {n m : ℕ} (scope : C.Slot n→Fin m) (hs : Function.Surjective scope)
    (v : Fin m) : scope (representative scope hs v)=v := (hs v).choose_spec

/-- Assigning one bit to each ordinary variable assigns one bit to each cycle. -/
def assignmentEquiv {n m : ℕ} (scope : C.Slot n→Fin m) (hs : Function.Surjective scope) :
    (Fin m→Bool) ≃ {a : C.Slot n→Bool // C.Consistent (next scope) a} where
  toFun x := ⟨fun s=>x (scope s),fun s=>congrArg x (scope_next scope s)⟩
  invFun a := fun v=>a.val (representative scope hs v)
  left_inv := by intro x; funext v; simp only [representative_scope]
  right_inv := by
    intro a
    apply Subtype.ext
    funext s
    exact consistent_fiber scope a.val a.property _ s (representative_scope scope hs _)

def value {K : Type*} [CommSemiring K] {n m : ℕ}
    (f : Signature K 2) (scope : C.Slot n→Fin m) : K :=
  ∑x : Fin m→Bool,∏v : Fin n,
    f ![x (scope (C.incidence v 0)),x (scope (C.incidence v 1))]

theorem cycle_value {K : Type*} [CommSemiring K] {n m : ℕ}
    (f : Signature K 2) (scope : C.Slot n→Fin m) (hs : Function.Surjective scope) :
    C.value f (next scope)=value f scope := by
  classical
  unfold C.value
  have hsum : (∑a : C.Slot n→Bool,if C.Consistent (next scope) a then C.weight f a else 0)=
      ∑a : {a : C.Slot n→Bool // C.Consistent (next scope) a},C.weight f a.val := by
    rw [←Finset.sum_filter]
    exact Finset.sum_subtype (p:=C.Consistent (next scope)) _ (by intro a; simp) (C.weight f)
  rw [hsum]
  symm
  apply Fintype.sum_equiv (assignmentEquiv scope hs)
  intro x
  rfl

/-- No free equality vertex occurs: the target consists only of the original
quaternary lift and structural X edges arranged by the computed cycles. -/
theorem native_value {K : Type*} [CommSemiring K] {n m : ℕ}
    (f : Signature K 2) (scope : C.Slot n→Fin m) (hs : Function.Surjective scope) :
    (C.network (EOBinaryPlaneCore.lift f) (next scope)).denote Fin.elim0=value f scope :=
  (C.denote_lift f (next scope)).trans (cycle_value f scope hs)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneCSP
