import Holant.ReedMuller.FlatNetwork.GenerationProgram

/-! Lifting a finite gate program by two untouched wires preserves the gate
restrictions and its length. The extra wires carry one repetition pair. -/
namespace Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.LowArity
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

@[simp] theorem binaryWeight_prepend_zero (s : BinaryVector n) :
    binaryWeight (prepend 0 s) = binaryWeight s := by
  simp only [binaryWeight, Finset.card_filter, Fin.sum_univ_succ, prepend,
    Fin.cons_zero, Fin.cons_succ]
  norm_num

def liftPermutation (e : Fin n ≃ Fin n) : Fin (n+2) ≃ Fin (n+2) where
  toFun := Fin.cons 0 (Fin.cons 1 (fun i => (e i).succ.succ))
  invFun := Fin.cons 0 (Fin.cons 1 (fun i => (e.symm i).succ.succ))
  left_inv := by
    intro i
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i
    · rfl
    · rfl
    · simp
  right_inv := by
    intro i
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i
    · rfl
    · rfl
    · simp

@[simp] theorem liftPermutation_zero (e : Fin n ≃ Fin n) : liftPermutation e 0 = 0 := rfl
@[simp] theorem liftPermutation_one (e : Fin n ≃ Fin n) : liftPermutation e 1 = 1 := rfl
@[simp] theorem liftPermutation_succ_succ (e : Fin n ≃ Fin n) (i : Fin n) :
    liftPermutation e i.succ.succ = (e i).succ.succ := rfl

@[simp] theorem dot_prepend_zero_right (x : BinaryVector (n+2)) (s : BinaryVector n) :
    dot x (prepend 0 s) = dot (dropTwo x) s := by
  rw [dot_comm, dot_prepend_arbitrary]
  simp [dot_comm]

@[simp] theorem transvection_prepend_zero_first (s : BinaryVector n) (x : BinaryVector (n+2)) :
    transvection (prepend 0 s) x 0 = x 0 := by simp [transvection, prepend]

@[simp] theorem transvection_prepend_zero_second (s : BinaryVector n) (x : BinaryVector (n+2)) :
    transvection (prepend 0 s) x 1 = x 1 := by simp [transvection, prepend]

@[simp] theorem dropTwo_transvection_prepend_zero (s : BinaryVector n) (x : BinaryVector (n+2)) :
    dropTwo (transvection (prepend 0 s) x) = transvection s (dropTwo x) := by
  funext i
  change x i.succ.succ + dot x (prepend 0 s) * s i =
    x i.succ.succ + dot (dropTwo x) s * s i
  rw [dot_prepend_zero_right]

namespace GenerationGate

def lift : GenerationGate n → GenerationGate (n+2)
  | .tau s h => .tau (prepend 0 s) (by simpa using h)
  | .perm e => .perm (liftPermutation e)

theorem lift_applyCode (g : GenerationGate n) (D : BinaryCode n) :
    g.lift.applyCode (pairExtension D) = pairExtension (g.applyCode D) := by
  ext x
  cases g with
  | tau s hs =>
    have his := weightFour_isotropic s hs
    have hil := weightFour_isotropic (prepend 0 s) (by simpa using hs)
    change x ∈ transvectionCode (prepend 0 s) (pairExtension D) ↔
      x ∈ pairExtension (transvectionCode s D)
    rw [mem_transvectionCode _ hil, mem_pairExtension, mem_pairExtension,
      mem_transvectionCode _ his]
    simp
  | perm e =>
    change (coordinateMap (liftPermutation e) x) 0 = (coordinateMap (liftPermutation e) x) 1 ∧
      dropTwo (coordinateMap (liftPermutation e) x) ∈ D ↔
      x 0 = x 1 ∧ coordinateMap e (dropTwo x) ∈ D
    rfl

end GenerationGate
namespace GenerationProgram

def lift (p : GenerationProgram n) : GenerationProgram (n+2) := p.map GenerationGate.lift

@[simp] theorem lift_length (p : GenerationProgram n) : p.lift.length = p.length := by simp [lift]

theorem lift_run (p : GenerationProgram n) (D : BinaryCode n) :
    p.lift.run (pairExtension D) = pairExtension (p.run D) := by
  induction p with
  | nil => rfl
  | cons g p ih =>
    change g.lift.applyCode (run (lift p) (pairExtension D)) =
      pairExtension (g.applyCode (run p D))
    rw [ih, GenerationGate.lift_applyCode]

end GenerationProgram
end
end Holant.ReedMuller.FlatNetwork
