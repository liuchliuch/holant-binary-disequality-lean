import Holant.Proofs.Hardness.EOBinaryPlaneScan

/-! The missing unused-variable factor for occurrence-cycle CSP compilation.
A full variable assignment is exactly one fiber-constant occurrence assignment
and one independent bit for each unused variable. The finite-sum identity is
valid for arbitrary finite variable/occurrence types and arbitrary weights.
Its native-EO specialization uses the literal opposite-pair lift only. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralCSPUnused
open Holant
open scoped BigOperators
namespace C
export EOBinaryPlaneCycles (Slot Consistent weight value network denote_lift)
end C
namespace S
export EOBinaryPlaneCSP (value next scope_next consistent_fiber)
end S
namespace Scan
export EOBinaryPlaneScan (next scope_forward consistent_fiber consistent_iff)
end Scan
set_option backward.isDefEq.respectTransparency false

variable {I V : Type*} [Fintype I] [Fintype V] [DecidableEq I] [DecidableEq V] (scope : I→V)

def FiberConstant (x : I→Bool) : Prop := ∀s t,scope s=scope t → x s=x t
abbrev Unused := {v : V // v∉Set.range scope}
local instance usedDecidable (v : V) : Decidable (v∈Set.range scope) := Classical.propDecidable _
local instance unusedDecidable (v : V) : Decidable (v∉Set.range scope) := Classical.propDecidable _
local instance constantDecidable (x : I→Bool) : Decidable (FiberConstant scope x) := Classical.propDecidable _
abbrev unusedCount := Fintype.card (Unused scope)
abbrev ConsistentAssignment := {x : I→Bool // FiberConstant scope x}

def assignmentEquiv : (V→Bool) ≃ (ConsistentAssignment scope × (Unused scope→Bool)) where
  toFun x := (⟨fun s=>x (scope s),fun s t h=>congrArg x h⟩,fun v=>x v.val)
  invFun p v := if hv : v∈Set.range scope then p.1.val (Classical.choose hv) else p.2 ⟨v,hv⟩
  left_inv x := by
    funext v
    by_cases hv : v∈Set.range scope
    · simp only [dif_pos hv]
      exact congrArg x (Classical.choose_spec hv)
    · simp only [dif_neg hv]
  right_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      funext s
      have hs : scope s∈Set.range scope := ⟨s,rfl⟩
      simp only [dif_pos hs]
      exact p.1.property _ s (Classical.choose_spec hs)
    · funext v
      simp only [dif_neg v.property]

/-- The weight sees only used variables. Every unused Boolean coordinate
contributes an independent factor of two, including the empty occurrence set. -/
theorem assignment_sum {K : Type*} [CommSemiring K] (w : (I→Bool)→K) :
    (∑x : V→Bool,w (fun s=>x (scope s)))=
      (2:K)^unusedCount scope * ∑x : ConsistentAssignment scope,w x.val := by
  classical
  calc
    _ = ∑p : ConsistentAssignment scope × (Unused scope→Bool),w p.1.val := by
      apply Fintype.sum_equiv (assignmentEquiv scope)
      intro x
      rfl
    _ = _ := by
      simp [Fintype.sum_prod_type,Fintype.card_fun,nsmul_eq_mul,←Finset.mul_sum]

theorem unusedCount_image :
    unusedCount scope=Fintype.card V-(Finset.univ.image scope).card := by
  classical
  have hu : Fintype.card {v : V // v∈Set.range scope}=(Finset.univ.image scope).card := by
    apply Fintype.card_of_subtype
    intro v
    simp
  change Fintype.card {v : V // ¬v∈Set.range scope}=_
  rw [Fintype.card_subtype_compl,hu]

section Binary
variable {n m : ℕ} (scope : C.Slot n→Fin m)

private theorem constant_iff (x : C.Slot n→Bool) :
    FiberConstant scope x ↔ C.Consistent (Scan.next scope) x := by
  constructor
  · intro h s
    exact h _ s (Scan.scope_forward scope s)
  · exact fun h=>Scan.consistent_fiber scope x h

/-- No surjectivity premise: the exact multiplier accounts for all omitted
ordinary variables while retaining the original occurrence graph. -/
theorem scan_cycle_value {K : Type*} [CommSemiring K] (f : Signature K 2) :
    S.value f scope=(2:K)^unusedCount scope*C.value f (Scan.next scope) := by
  classical
  have hcycle : C.value f (Scan.next scope)=
      ∑x : ConsistentAssignment scope,C.weight f x.val := by
    unfold C.value
    simp only [←constant_iff]
    rw [←Finset.sum_filter]
    exact Finset.sum_subtype (p:=FiberConstant scope) _ (by intro x; simp) (C.weight f)
  rw [hcycle]
  exact assignment_sum scope (C.weight f)

theorem abstract_cycle_value {K : Type*} [CommSemiring K] (f : Signature K 2) :
    S.value f scope=(2:K)^unusedCount scope*C.value f (S.next scope) := by
  rw [scan_cycle_value scope f]
  apply congrArg (fun z : K=>(2:K)^unusedCount scope*z)
  unfold C.value
  apply Finset.sum_congr rfl
  intro x _
  rw [Scan.consistent_iff scope x]

/-- The physical query uses only the literal lifted signature and native X.
Unused variables are restored multiplicatively from its returned answer. -/
theorem native_value {K : Type*} [CommSemiring K] (f : Signature K 2) :
    S.value f scope=(2:K)^unusedCount scope*
      (C.network (EOBinaryPlaneCore.lift f) (Scan.next scope)).denote Fin.elim0 := by
  rw [C.denote_lift]
  exact scan_cycle_value scope f

/-- A total executable list count for the scalar-correction programme. -/
def unusedVariables : List (Fin m) :=
  (List.finRange m).filter (fun v=> !(List.ofFn scope).contains v)

theorem mem_unusedVariables (v : Fin m) : v∈unusedVariables scope ↔ v∉Set.range scope := by
  simp [unusedVariables,Set.mem_range,List.mem_ofFn]

theorem unusedVariables_nodup : (unusedVariables scope).Nodup :=
  (List.nodup_finRange m).filter _

theorem unusedCount_list : unusedCount scope=(unusedVariables scope).length := by
  classical
  rw [←List.toFinset_card_of_nodup (unusedVariables_nodup scope)]
  apply Fintype.card_of_subtype
  intro v
  simpa using mem_unusedVariables scope v

end Binary
end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralCSPUnused
