import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentTableLoopRun

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentTableLoop
open Turing Computability BinaryCompose FixedFieldMachines
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option Elab.async false
variable {s b : ℕ} {arity : ℕ → ℕ}

abbrev packageEncoding := EdgeTableLoop.packageEncoding
def value (x : {r : RawClosedNetwork // r.WellFormed s b arity}) := (x.val.graph x.property).parentTable

noncomputable def timed_package (w : Computes (RawParentRow.inputEncoding s b arity) ParentRowEncoding.row RawParentRow.value)
    (x : {r : RawClosedNetwork // r.WellFormed s b arity}) :
    TM2OutputsInTime (machine w.machine).computer ((packageEncoding s b arity).encode x)
      (some (ParentRowEncoding.table.encode (value x)))
      ((timePolynomial w).eval (RawClosedNetwork.encoding.encode x.val).length) where
  steps := Classical.choose (package_run w x.val x.property)
  evals_in_steps := (Classical.choose_spec (package_run w x.val x.property)).2
  steps_le_m := (Classical.choose_spec (package_run w x.val x.property)).1

noncomputable def computes (w : Computes (RawParentRow.inputEncoding s b arity) ParentRowEncoding.row RawParentRow.value) :
    Computes (packageEncoding s b arity) ParentRowEncoding.table value where
  machine := machine w.machine
  time := timePolynomial w
  outputs x := {
    steps := (timed_package w x).steps
    evals_in_steps := (timed_package w x).evals_in_steps
    steps_le_m := le_trans (timed_package w x).steps_le_m
      (natPolynomial_eval_mono (timePolynomial w) (EdgeTableLoop.raw_length_le_package x)) }
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentTableLoop
