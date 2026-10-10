import Holant.Proofs.Counting.Circuit
import Holant.Complexity.EdgeSubdivision.WirePath


namespace Holant.LocalDrafts.CountingHardness.GateAlphabet

open Holant Holant.Complexity
open scoped BigOperators

def arity : ℕ → ℕ
  | 0 | 1 | 2 => 1
  | _ => 3

def free {K : Type*} [One K] : Signature K 1 := fun _ => 1

def pin {K : Type*} [Zero K] [One K] (b : Bool) : Signature K 1 :=
  fun x => if x 0 = b then 1 else 0

def copy {K : Type*} [Zero K] [One K] : Signature K 3 :=
  fun x => if x 0 = x 1 ∧ x 1 = x 2 then 1 else 0

def nand {K : Type*} [Zero K] [One K] : Signature K 3 :=
  fun x => if x 2 = !(x 0 && x 1) then 1 else 0

def signatures {K : Type*} [Zero K] [One K] :
    (i : Fin 5) → Signature K (arity i.val) := fun i =>
  match i with
  | ⟨0, _⟩ => free
  | ⟨1, _⟩ => pin false
  | ⟨2, _⟩ => pin true
  | ⟨3, _⟩ => copy
  | ⟨4, _⟩ => nand
  | ⟨k + 5, h⟩ => False.elim (by omega)

def equality {K : Type*} [Zero K] [One K] (a b : Bool) : K := if a = b then 1 else 0

theorem equality_kernel {K : Type*} [CommSemiring K] (a b : Bool) :
    equality (K := K) a b = EdgeSubdivision.WirePath.kernel false a b := by
  cases a <;> cases b <;> rfl

section LocalContraction
variable {K : Type*} [CommSemiring K]

theorem wire_contract (a : Bool) (f : Bool → K) :
    (∑ b, equality a b * f b) = f a := by
  cases a <;> simp [Fintype.sum_bool, equality]

/-- Both output ports are determined by the one input bit, even if their
downstream destinations will be two ports of the same NAND occurrence. -/
theorem copy_contract (a : Bool) (f : Bool → Bool → K) :
    (∑ b : Bool, ∑ c : Bool, copy ![a, b, c] * f b c) = f a a := by
  cases a <;> simp [Fintype.sum_bool, copy]

theorem nand_contract (a b : Bool) (f : Bool → K) :
    (∑ c : Bool, nand ![a, b, c] * f c) = f (!(a && b)) := by
  cases a <;> cases b <;> simp [Fintype.sum_bool, nand]

theorem pin_contract (a : Bool) (f : Bool → K) :
    (∑ b : Bool, pin a ![b] * f b) = f a := by
  cases a <;> simp [Fintype.sum_bool, pin]

/-- Retaining an ignored input is necessary: its two original witnesses remain. -/
theorem ignored_wire : (∑ a : Bool, ∑ b : Bool,
    (free ![a] : K) * equality a b * free ![b]) = 2 := by
  simp [Fintype.sum_bool, free, equality, one_add_one_eq_two]

/-- A literal X vertex on one end of an X edge realizes equality exactly.
This scalar-one identity does not identify X with equality. -/
theorem native_x_wire (a c : Bool) :
    (∑ b : Bool, EdgeSubdivision.WirePath.kernel (K := K) true a b *
      EdgeSubdivision.WirePath.kernel true b c) = equality a c := by
  cases a <;> cases c <;>
    simp [Fintype.sum_bool, EdgeSubdivision.WirePath.kernel, equality]

end LocalContraction
end Holant.LocalDrafts.CountingHardness.GateAlphabet
