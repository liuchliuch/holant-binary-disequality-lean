import Holant.Proofs.CountingMachines.CircuitNative.Circuit
import Holant.Complexity.EdgeSubdivision.WirePath
import Holant.Proofs.CountingMachines.Interface


namespace Holant.LocalDrafts.RemoteWork.CountingBridge.GateAlphabet

open Holant Holant.Complexity
open scoped BigOperators

abbrev arity := Gates.arity
abbrev free {K : Type*} [One K] : Signature K 1 := Gates.free
abbrev pin {K : Type*} [Zero K] [One K] (b : Bool) : Signature K 1 := Gates.pin b
abbrev copy {K : Type*} [Zero K] [One K] : Signature K 3 := Gates.copy
abbrev nand {K : Type*} [Zero K] [One K] : Signature K 3 := Gates.nand
abbrev signatures {K : Type*} [Zero K] [One K] :
    (i : Fin 5) → Signature K (arity i.val) := Gates.signatures

@[simp] theorem arity_interface : arity = Gates.arity := rfl
@[simp] theorem signatures_interface {K : Type*} [Zero K] [One K] :
    signatures (K := K) = Gates.signatures := rfl

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
  cases a <;> simp [Fintype.sum_bool, copy, Gates.copy]

theorem nand_contract (a b : Bool) (f : Bool → K) :
    (∑ c : Bool, nand ![a, b, c] * f c) = f (!(a && b)) := by
  cases a <;> cases b <;> simp [Fintype.sum_bool, nand, Gates.nand]

theorem pin_contract (a : Bool) (f : Bool → K) :
    (∑ b : Bool, pin a ![b] * f b) = f a := by
  cases a <;> simp [Fintype.sum_bool, pin, Gates.pin]

/-- Retaining an ignored input is necessary: its two original witnesses remain. -/
theorem ignored_wire : (∑ a : Bool, ∑ b : Bool,
    (free ![a] : K) * equality a b * free ![b]) = 2 := by
  simp [Fintype.sum_bool, free, Gates.free, equality, one_add_one_eq_two]

/-- A literal X vertex on one end of an X edge realizes equality exactly.
This scalar-one identity does not identify X with equality. -/
theorem native_x_wire (a c : Bool) :
    (∑ b : Bool, EdgeSubdivision.WirePath.kernel (K := K) true a b *
      EdgeSubdivision.WirePath.kernel true b c) = equality a c := by
  cases a <;> cases c <;>
    simp [Fintype.sum_bool, EdgeSubdivision.WirePath.kernel, equality]

end LocalContraction
end Holant.LocalDrafts.RemoteWork.CountingBridge.GateAlphabet
