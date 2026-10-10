import Holant.Proofs.Hardness.EOBinaryPlaneCSP
import Mathlib.Data.Fintype.Prod

/-! The exact cut/degree extraction behind zero-field Ising to independent sets.
An apex removes the need for free local pins. Its two orientations contribute
exactly one global factor 2, including the empty graph. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneIsing
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

variable {n m : ℕ}

def cut (left right : Fin n→Fin m) (x : Fin m→Bool) : ℕ :=
  ∑e,(Bool.xor (x (left e)) (x (right e))).toNat

def degree (left right : Fin n→Fin m) (x : Fin m→Bool) : ℕ :=
  ∑e,((x (left e)).toNat+(x (right e)).toNat)

def internal (left right : Fin n→Fin m) (x : Fin m→Bool) : ℕ :=
  ∑e,if x (left e)=true ∧ x (right e)=true then 1 else 0

def Independent (left right : Fin n→Fin m) (x : Fin m→Bool) : Prop :=
  ∀e,¬(x (left e)=true ∧ x (right e)=true)

theorem cut_internal (left right : Fin n→Fin m) (x : Fin m→Bool) :
    cut left right x+2*internal left right x=degree left right x := by
  unfold cut internal degree
  rw [Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  cases x (left e) <;> cases x (right e) <;> decide

theorem internal_zero (left right : Fin n→Fin m) (x : Fin m→Bool) :
    internal left right x=0 ↔ Independent left right x := by
  classical
  simp [internal,Independent]

theorem diagonal_iff (left right : Fin n→Fin m) (x : Fin m→Bool) :
    cut left right x=degree left right x ↔ Independent left right x := by
  rw [←internal_zero]
  have h := cut_internal left right x
  omega

theorem cut_bound (left right : Fin n→Fin m) (x : Fin m→Bool) : cut left right x≤n := by
  calc
    cut left right x≤∑_e : Fin n,(1 : ℕ) := by
      apply Finset.sum_le_sum
      intro e _
      cases Bool.xor (x (left e)) (x (right e)) <;> decide
    _=n := by simp

theorem degree_bound (left right : Fin n→Fin m) (x : Fin m→Bool) : degree left right x≤2*n := by
  calc
    degree left right x≤∑_e : Fin n,(2 : ℕ) := by
      apply Finset.sum_le_sum
      intro e _
      cases x (left e) <;> cases x (right e) <;> decide
    _=2*n := by simp [Nat.mul_comm]

/-- Apex-relative bits are invariant under flipping every spin. -/
def relative (z : Fin (m+1)→Bool) : Fin m→Bool := fun i=>Bool.xor (z 0) (z i.succ)

def apexAssignments (m : ℕ) : (Fin (m+1)→Bool) ≃ (Bool×(Fin m→Bool)) where
  toFun z := (z 0,relative z)
  invFun p := Fin.cons p.1 (fun i=>Bool.xor p.1 (p.2 i))
  left_inv := by
    intro z
    funext i
    refine Fin.cases ?_ (fun j=>?_) i
    · rfl
    · change Bool.xor (z 0) (Bool.xor (z 0) (z j.succ))=z j.succ
      cases z 0 <;> cases z j.succ <;> rfl
  right_inv := by
    rintro ⟨b,x⟩
    change (b,fun i=>Bool.xor b (Bool.xor b (x i)))=(b,x)
    congr 1
    funext i
    cases b <;> cases x i <;> rfl

theorem relative_apex (b : Bool) (x : Fin m→Bool) :
    relative ((apexAssignments m).symm (b,x))=x := by
  exact congrArg Prod.snd ((apexAssignments m).apply_symm_apply (b,x))

/-- Any statistic of apex-relative spins has exactly two copies in the unpinned
zero-field sum; no factor per connected component or vertex is inserted. -/
theorem apex_sum {K : Type*} [CommSemiring K] (f : (Fin m→Bool)→K) :
    (∑z : Fin (m+1)→Bool,f (relative z))=2*∑x : Fin m→Bool,f x := by
  classical
  let : Fintype (Bool×(Fin m→Bool)) := @instFintypeProd _ _ Bool.fintype inferInstance
  calc
    _=∑p : Bool×(Fin m→Bool),f p.2 := by
      apply Fintype.sum_equiv (apexAssignments m)
      intro z
      rfl
    _=_ := by simp [Fintype.sum_prod_type,two_mul]

def independentCount (left right : Fin n→Fin m) : ℕ := by
  classical
  exact ∑x : Fin m→Bool,if Independent left right x then 1 else 0

/-- Selecting the diagonal cut=selected-degree coefficients counts independent
sets, with the exact apex-flip factor. Loops and repeated edges are retained. -/
theorem diagonal_count (left right : Fin n→Fin m) :
    (∑z : Fin (m+1)→Bool,
      if cut left right (relative z)=degree left right (relative z) then 1 else 0)=
      2*independentCount left right := by
  classical
  simp only [diagonal_iff]
  exact apex_sum (fun x=>if Independent left right x then (1 : ℕ) else 0)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneIsing
