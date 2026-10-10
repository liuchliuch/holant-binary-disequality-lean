import Holant.Dihedral.SupportIntegration.Patch

/-! Original-port transport for the reconstructed code. Equality of global
directions is derived from equality of their full affine supports. -/
noncomputable section
namespace Holant.Dihedral.SupportIntegration
open Holant.Dihedral.EndpointParallelogram Holant.ReedMuller.LowArity
variable {n : ℕ}

 def pull (o : Equiv.Perm (Fin n)) : BinaryVector n ≃ₗ[ZMod 2] BinaryVector n where
  toFun x i := x (o i)
  invFun x i := x (o.symm i)
  left_inv := by intro x; funext i; simp
  right_inv := by intro x; funext i; simp
  map_add' := by intro x y; rfl
  map_smul' := by intro c x; rfl

 @[simp] theorem pull_apply (o : Equiv.Perm (Fin n)) (x : BinaryVector n) (i : Fin n) :
    pull o x i=x (o i) := rfl
 @[simp] theorem pull_symm_pull (o : Equiv.Perm (Fin n)) (x : BinaryVector n) :
    pull o.symm (pull o x)=x := by funext i; simp
 @[simp] theorem pull_pull_symm (o : Equiv.Perm (Fin n)) (x : BinaryVector n) :
    pull o (pull o.symm x)=x := by funext i; simp

 def reindexCode (o : Equiv.Perm (Fin n)) (L : BinaryCode n) : BinaryCode n :=
  L.comap (pull o).toLinearMap

 theorem fullCoset_reindex {K : Type*} [Field K] (F : BinaryVector n → K)
    (o : Equiv.Perm (Fin n)) (L : BinaryCode n) (a : BinaryVector n)
    (hf : fullCoset (fun x => F (pull o.symm x)) L a) :
    fullCoset F (reindexCode o L) (pull o.symm a) := by
  intro x
  have hh := hf (pull o x)
  change F (pull o.symm (pull o x)) ≠ 0 ↔ pull o x ∈ coset L a at hh
  rw [pull_symm_pull] at hh
  change F x ≠ 0 ↔ pull o (x+pull o.symm a) ∈ L
  rw [(pull o).map_add,pull_pull_symm]
  exact hh

 theorem fullCoset_direction_unique {K : Type*} [Field K] (F : BinaryVector n → K)
    (L M : BinaryCode n) (a b : BinaryVector n)
    (hL : fullCoset F L a) (hM : fullCoset F M b) : L=M := by
  apply coset_direction_unique L M a b
  ext x
  exact (hL x).symm.trans (hM x)

end Holant.Dihedral.SupportIntegration
