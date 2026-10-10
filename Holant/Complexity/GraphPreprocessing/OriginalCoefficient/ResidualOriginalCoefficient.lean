import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualContext
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualStoredCoefficient
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualZeroCoefficientSpec
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ChildInputWiring

/-! Original conditioned a/b coefficients from a retained raw/cut context and
an original vertex. The canonical parent row is physically computed inside the
b producer; the source unused-edge invariant proves descriptor validity. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualOriginalCoefficient
open Turing Computability BinaryCompose FixedFieldMachines
open Holant.OneHot.StackProgram.GraphLabelEncoding
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false
variable {s b : ℕ} {arity : ℕ → ℕ}

def prepared (x : ResidualContext.Query s b arity) : ResidualStoredCoefficient.Input s b arity :=
  ⟨⟨ParentCoefficient.originalInput (ResidualContext.original x),ResidualContext.edge x.1⟩,x.1.property x.2⟩
noncomputable def prepareComputes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (ResidualContext.queryEncoding s b arity) (ResidualStoredCoefficient.inputEncoding s b arity) prepared :=
  recode (pairComputes ((ResidualContext.originalComputes s b arity).andThen (ParentCoefficient.originalPrepare s b arity))
    (ResidualContext.edgeComputes s b arity)) id (fun _ => rfl) (fun _ => rfl)
def parentValue (a z : Bool) (x : ResidualContext.Query s b arity) := ResidualStoredCoefficient.value false a z (prepared x)
noncomputable def parentComputes (a z : Bool) (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (ResidualContext.queryEncoding s b arity) (treeLabelEncoding s b arity) (parentValue a z) :=
  (prepareComputes s b arity).andThen (ResidualStoredCoefficient.computes false a z s b arity)
abbrev prepareMachine := pairMachine
  (ResidualContext.originalMachine.compose (pairMachine identityMachine RawParentRow.machine)) ResidualContext.edgeMachine
abbrev parentMachine (a z : Bool) (s b : ℕ) (arity : ℕ → ℕ) :=
  prepareMachine.compose (ResidualStoredCoefficient.machine false a z s b arity)
@[simp] theorem parent_machine (a z : Bool) (s b : ℕ) (arity : ℕ → ℕ) : (parentComputes a z s b arity).machine=parentMachine a z s b arity := rfl
theorem parent_inFP (a z : Bool) : InFP (ResidualContext.queryEncoding s b arity) (treeLabelEncoding s b arity) (parentValue a z) :=
  (parentComputes a z s b arity).inFP

def zeroQuery (x : ResidualContext.Query s b arity) : ResidualPinQuery.Input s b arity :=
  ⟨ResidualContext.source x.1,x.2,ResidualContext.edge x.1⟩
noncomputable def zeroPrepare (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (ResidualContext.queryEncoding s b arity) (ResidualPinQuery.inputEncoding s b arity) zeroQuery :=
  recode ChildInputWiring.computes
    (fun x => ((RawClosedNetwork.encoding.encode (ResidualContext.source x.1).val,encodeNat (ResidualContext.edge x.1).val),List.replicate x.2.val true))
    (fun _ => rfl) (fun _ => rfl)
def zeroValue (a z : Bool) (x : ResidualContext.Query s b arity) := ResidualZeroCoefficient.literal a z (zeroQuery x)
noncomputable def zeroComputes (a z : Bool) (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (ResidualContext.queryEncoding s b arity) (treeLabelEncoding s b arity) (zeroValue a z) :=
  (zeroPrepare s b arity).andThen (ResidualZeroCoefficient.computes s b arity a z)
abbrev zeroMachine (a z : Bool) (s b : ℕ) (arity : ℕ → ℕ) :=
  ChildInputWiring.machine.compose (ResidualZeroCoefficient.machine s b arity a z)
@[simp] theorem zero_machine (a z : Bool) (s b : ℕ) (arity : ℕ → ℕ) : (zeroComputes a z s b arity).machine=zeroMachine a z s b arity := rfl
theorem zero_inFP (a z : Bool) : InFP (ResidualContext.queryEncoding s b arity) (treeLabelEncoding s b arity) (zeroValue a z) :=
  (zeroComputes a z s b arity).inFP

theorem zero_conditioned (a z : Bool) (x : ResidualContext.Query s b arity) :
    zeroValue a z x=
      ((((ResidualContext.source x.1).val.labelNetwork (ResidualContext.source x.1).property).asFinite).executableConditionEdge
        (ResidualContext.edge x.1) a z).vertex x.2 (fun _ => false) :=
  ResidualZeroCoefficient.literal_eq_conditioned_zero a z (zeroQuery x)
theorem parent_conditioned (a z : Bool) (x : ResidualContext.Query s b arity) :
    parentValue a z x=
      ((((ResidualContext.source x.1).val.labelNetwork (ResidualContext.source x.1).property).asFinite).executableConditionEdge
        (ResidualContext.edge x.1) a z).vertex x.2
        (ResidualParentCoefficient.survivingWord (ResidualStoredCoefficient.prepared false (prepared x))) :=
  ResidualStoredCoefficient.value_conditioned false a z (prepared x)

noncomputable def parentTimePolynomial (a z : Bool) (s b : ℕ) (arity : ℕ → ℕ) : Polynomial ℕ :=
  (parentComputes a z s b arity).time.comp (7*(Polynomial.X+1))
noncomputable def parent_timed (a z : Bool) (x : ResidualContext.Query s b arity) :
    TM2OutputsInTime (parentMachine a z s b arity).computer ((ResidualContext.queryEncoding s b arity).encode x)
      (some ((treeLabelEncoding s b arity).encode (parentValue a z x)))
      ((parentTimePolynomial a z s b arity).eval (RawClosedNetwork.encoding.encode (ResidualContext.source x.1).val).length) where
  steps := ((parentComputes a z s b arity).outputs x).steps
  evals_in_steps := ((parentComputes a z s b arity).outputs x).evals_in_steps
  steps_le_m := by
    have h := natPolynomial_eval_mono (parentComputes a z s b arity).time (ResidualContext.query_length x)
    exact le_trans ((parentComputes a z s b arity).outputs x).steps_le_m (by simpa [parentTimePolynomial] using h)
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualOriginalCoefficient
