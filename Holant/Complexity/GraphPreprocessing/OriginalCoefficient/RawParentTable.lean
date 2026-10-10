import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentTableLoopInterface

/-! A complete physical canonical parent-table producer from original raw
network bytes. The executed original vertex count drives the loop; rows retain
original vertex order, least component roots, first-hit depths and original
edge/end identities. No parent, component or size table is supplied as input. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RawParentTable
open Turing Computability BinaryCompose FixedFieldMachines
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false
variable {s b : ℕ} {arity : ℕ → ℕ}

abbrev Input (s b : ℕ) (arity : ℕ → ℕ) := {r : RawClosedNetwork // r.WellFormed s b arity}
def value (x : Input s b arity) := (x.val.graph x.property).parentTable
abbrev machine : Machine := CountsPackage.machine.compose (ParentTableLoop.machine RawParentRow.machine)
noncomputable def computes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (RawClosedNetwork.validatedEncoding s b arity) ParentRowEncoding.table value :=
  (RawEdgeTable.countsComputes s b arity).andThen (ParentTableLoop.computes (RawParentRow.computes s b arity))
@[simp] theorem computes_machine (s b : ℕ) (arity : ℕ → ℕ) : (computes s b arity).machine=machine := rfl
noncomputable def timePolynomial (s b : ℕ) (arity : ℕ → ℕ) : Polynomial ℕ := (computes s b arity).time
noncomputable def timed (x : Input s b arity) :
    TM2OutputsInTime machine.computer (RawClosedNetwork.encoding.encode x.val)
      (some (ParentRowEncoding.table.encode (value x)))
      ((timePolynomial s b arity).eval (RawClosedNetwork.encoding.encode x.val).length) := (computes s b arity).outputs x

theorem inFP : InFP (RawClosedNetwork.validatedEncoding s b arity) ParentRowEncoding.table value := (computes s b arity).inFP
noncomputable def primitivePolynomial (s b : ℕ) (arity : ℕ → ℕ) : Polynomial ℕ :=
  timePolynomial s b arity*Polynomial.C machine.primitiveBudget
theorem primitive_bound (x : Input s b arity) :
    primitiveCost machine (timed x).steps (some (initList machine.computer (RawClosedNetwork.encoding.encode x.val))) ≤
      (primitivePolynomial s b arity).eval (RawClosedNetwork.encoding.encode x.val).length := by
  have h := Nat.mul_le_mul_right machine.primitiveBudget (timed x).steps_le_m
  simpa only [primitivePolynomial,Polynomial.eval_mul,Polynomial.eval_C] using le_trans (primitiveCost_le _ _ _) h
@[simp] theorem value_length (x : Input s b arity) : (value x).length=x.val.vertices.length := by
  simp [value,RawClosedNetwork.graph]

/-- The physical retained-input package directly supplies original-row/port
consumers with the original bytes and the freshly computed canonical table. -/
noncomputable def retainedComputes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (RawClosedNetwork.validatedEncoding s b arity)
      (pairEncoding (RawClosedNetwork.validatedEncoding s b arity) ParentRowEncoding.table) (fun x => (x,value x)) :=
  pairComputes (identityComputes (RawClosedNetwork.validatedEncoding s b arity)) (computes s b arity)
abbrev retainedMachine : Machine := pairMachine identityMachine machine
@[simp] theorem retainedComputes_machine (s b : ℕ) (arity : ℕ → ℕ) : (retainedComputes s b arity).machine=retainedMachine := rfl

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RawParentTable
