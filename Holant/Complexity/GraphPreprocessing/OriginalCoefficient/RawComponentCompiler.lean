import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RawTreeCompiler
import Holant.Complexity.GraphPreprocessing.CanonicalExpansion.Component
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RawComponentLabel

/-! Raw bytes to the exact canonical component spanning-tree bytecode. The
least original component root is physically found before table generation and
compilation. This is the tree branch of the graph compiler; cyclic components
still require their separate residual/dense classification and assembly. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RawComponentCompiler
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines CanonicalStability
open Holant.OneHot Holant.OneHot.StackProgram Holant.OneHot.StackProgram.GraphLabelEncoding
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false
variable {s b : ℕ} {arity : ℕ → ℕ}

def Canonical (x : RawRootReach.Input s b arity) : Prop := (x.1.val.graph x.1.property).label x.2=x.2
instance (x : RawRootReach.Input s b arity) : Decidable (Canonical x) := inferInstanceAs (Decidable (_=_))
abbrev CanonicalInput (s b : ℕ) (arity : ℕ → ℕ) := {x : RawRootReach.Input s b arity // Canonical x}
def canonicalEncoding (s b : ℕ) (arity : ℕ → ℕ) : Encoding (CanonicalInput s b arity) Bool where
  encode x := (RawRootReach.inputEncoding s b arity).encode x.val
  decode bits := do
    let x ← (RawRootReach.inputEncoding s b arity).decode bits
    if h : Canonical x then some ⟨x,h⟩ else none
  decode_encode x := by simp [x.property]
def canonicalValue (x : CanonicalInput s b arity) : Code (RawClosedNetwork.TreeLabel s b arity) :=
  computedTreeCode ((x.val.1.val.labelNetwork x.val.1.property).computedComponentNetwork x.val.2) none
    (componentRoot (x.val.1.val.labelNetwork x.val.1.property) x.val.2)
    (component_connected (x.val.1.val.labelNetwork x.val.1.property) x.val.2)

/-- Literal expansion and the original-V count bound are derived from the raw
network. They are not assumptions or additional data at this entry. -/
theorem canonical_run (x : CanonicalInput s b arity) :
    ∃ time, time≤(RawTreeCompiler.timePolynomial s b arity).eval (RawClosedNetwork.encoding.encode x.val.1.val).length ∧
      RunsExactly (RawTreeCompiler.machine s b arity).computer.step
        (initList (RawTreeCompiler.machine s b arity).computer ((canonicalEncoding s b arity).encode x))
        (haltList (RawTreeCompiler.machine s b arity).computer ((codeEncoding (treeLabelEncoding s b arity)).encode (canonicalValue x))) time := by
  let parts := CanonicalExpansion.closedParts (CanonicalExpansion.componentTreeValue x.val.1.val x.val.1.property x.val.2)
  obtain ⟨hexpand,hcount⟩ := CanonicalExpansion.raw_component_closed x.val.1.val x.val.1.property x.val.2 x.property
  obtain ⟨time,ht,run⟩ := RawTreeCompiler.closed_execute s b arity x.val parts.1 parts.2 _ hexpand hcount
  have code := CanonicalExpansion.component_code x.val.1.val x.val.1.property x.val.2
  change compileClosed parts.1 parts.2=canonicalValue x at code
  rw [code] at run
  exact ⟨time,ht,run⟩

noncomputable def canonicalComputes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (canonicalEncoding s b arity) (codeEncoding (treeLabelEncoding s b arity)) canonicalValue where
  machine := RawTreeCompiler.machine s b arity
  time := RawTreeCompiler.timePolynomial s b arity
  outputs x := {
    steps := Classical.choose (canonical_run x)
    evals_in_steps := (Classical.choose_spec (canonical_run x)).2
    steps_le_m := le_trans (Classical.choose_spec (canonical_run x)).1
      (natPolynomial_eval_mono _ (by
        change (RawClosedNetwork.encoding.encode x.val.1.val).length≤
          (Holant.Algebraic.frame (RawClosedNetwork.encoding.encode x.val.1.val)++List.replicate x.val.2.val true).length
        simp only [List.length_append,Holant.Algebraic.frame_length,List.length_replicate]
        omega)) }

def normalized (x : RawRootReach.Input s b arity) : CanonicalInput s b arity :=
  ⟨⟨x.1,(x.1.val.graph x.1.property).label x.2⟩,(x.1.val.graph x.1.property).label_idempotent x.2⟩
noncomputable def rawComputes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (RawRootReach.inputEncoding s b arity) (RawClosedNetwork.validatedEncoding s b arity) Sigma.fst :=
  recode (Wiring.firstComputes (RawClosedNetwork.validatedEncoding s b arity) UnaryBinary.unaryEncoding)
    (fun x => (x.1,x.2.val)) (fun _ => rfl) (fun _ => rfl)
noncomputable def normalizeComputes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (RawRootReach.inputEncoding s b arity) (canonicalEncoding s b arity) normalized :=
  recode (pairComputes (rawComputes s b arity) (RawComponentLabel.computes s b arity)) id (fun _ => rfl) (fun _ => rfl)
def value (x : RawRootReach.Input s b arity) := canonicalValue (normalized x)
noncomputable def computes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (RawRootReach.inputEncoding s b arity) (codeEncoding (treeLabelEncoding s b arity)) value :=
  (normalizeComputes s b arity).andThen (canonicalComputes s b arity)
abbrev normalizeMachine : Machine := pairMachine Wiring.firstMachine RawComponentLabel.machine
abbrev machine (s b : ℕ) (arity : ℕ → ℕ) := normalizeMachine.compose (RawTreeCompiler.machine s b arity)
@[simp] theorem computes_machine (s b : ℕ) (arity : ℕ → ℕ) : (computes s b arity).machine=machine s b arity := rfl
theorem inFP : InFP (RawRootReach.inputEncoding s b arity) (codeEncoding (treeLabelEncoding s b arity)) value := (computes s b arity).inFP

noncomputable def timePolynomial (s b : ℕ) (arity : ℕ → ℕ) : Polynomial ℕ := (computes s b arity).time.comp (3*(Polynomial.X+1))
noncomputable def timed (x : RawRootReach.Input s b arity) :
    TM2OutputsInTime (machine s b arity).computer ((RawRootReach.inputEncoding s b arity).encode x)
      (some ((codeEncoding (treeLabelEncoding s b arity)).encode (value x)))
      ((timePolynomial s b arity).eval (RawClosedNetwork.encoding.encode x.1.val).length) where
  steps := ((computes s b arity).outputs x).steps
  evals_in_steps := ((computes s b arity).outputs x).evals_in_steps
  steps_le_m := by
    have h := natPolynomial_eval_mono (computes s b arity).time (RawRootReach.input_length_le_original x)
    exact le_trans ((computes s b arity).outputs x).steps_le_m (by simpa [timePolynomial] using h)
noncomputable def primitivePolynomial (s b : ℕ) (arity : ℕ → ℕ) : Polynomial ℕ :=
  timePolynomial s b arity*Polynomial.C (machine s b arity).primitiveBudget
theorem primitive_bound (x : RawRootReach.Input s b arity) :
    primitiveCost (machine s b arity) (timed x).steps
      (some (initList (machine s b arity).computer ((RawRootReach.inputEncoding s b arity).encode x))) ≤
      (primitivePolynomial s b arity).eval (RawClosedNetwork.encoding.encode x.1.val).length := by
  have h := Nat.mul_le_mul_right (machine s b arity).primitiveBudget (timed x).steps_le_m
  simpa only [primitivePolynomial,Polynomial.eval_mul,Polynomial.eval_C] using le_trans (primitiveCost_le _ _ _) h
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RawComponentCompiler
