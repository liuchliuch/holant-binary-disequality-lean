import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentSearchInterface
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RootBitmapInterface

/-! A clean bounded parent/depth machine starting with an original vertex count,
root, target and edge table. Its singleton bitmap and round counter are both
physically constructed. This entry handles connected nonroot queries. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RootedNonroot
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
open Holant.OneHot.Computable
open Holant.OneHot.StackProgram.GraphLabelEncoding
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option synthInstance.maxSize 2048
set_option Elab.async false

abbrev Base := Σ root : RootBitmap.Input, Fin root.1 × List (Fin root.1 × Fin root.1)
def baseEncoding : Encoding Base Bool := sigmaEncoding RootBitmap.inputEncoding
  (fun r => pairEncoding (OccurrenceLabel.unaryPortEncoding r.1) (NeighborScan.edgeEncoding r.1))
def baseGraph (x : Base) : Graph := ⟨x.1.1,x.2.2⟩
def Valid (x : Base) : Prop := x.2.1∈(baseGraph x).reach x.1.2 x.1.1 ∧ x.2.1≠x.1.2
instance (x : Base) : Decidable (Valid x) := inferInstanceAs (Decidable (_ ∧ _))
abbrev Input := {x : Base // Valid x}
def inputEncoding : Encoding Input Bool where
  encode x := baseEncoding.encode x.val
  decode bits := do
    let x ← baseEncoding.decode bits
    if h : Valid x then some ⟨x,h⟩ else none
  decode_encode x := by simp [x.property]

def graph (x : Input) : Graph := baseGraph x.val
def root (x : Input) : (graph x).Vertex := x.val.1.2
def target (x : Input) : (graph x).Vertex := x.val.2.1
def vertex (x : Input) : {v : (graph x).Fiber (root x) // v≠(graph x).fiberRoot (root x)} :=
  ⟨⟨target x,x.property.1⟩,fun h => x.property.2 (congrArg Subtype.val h)⟩

def initialWord (x : Input) : List Bool := ParentSearch.word (graph x) {root x} (target x)
def value (x : Input) : ℕ × Option (ℕ × Bool) :=
  ((graph x).depth (root x) (vertex x).val,
    some (((graph x).parentEnd (root x) (vertex x)).1.val,((graph x).parentEnd (root x) (vertex x)).2))
def outputEncoding := pairEncoding UnaryBinary.unaryEncoding ParentRowEncoding.parent

theorem initial_word (x : Input) : initialWord x =
    Holant.Algebraic.frame (RootBitmap.value x.val.1)++ParentSearch.tailWord (graph x) (target x) := by
  have h := RootBitmap.graph_value (graph x) (root x)
  change RootBitmap.value x.val.1 = NeighborPredicate.bitmap (graph x) {root x} at h
  unfold initialWord ParentSearch.word
  rw [←h]

abbrev rootMachine : Machine := LeftMap.machine RootBitmap.machine
abbrev machine : Machine := rootMachine.compose (ParentSearch.machine ParentSearch.actual)
noncomputable def rootComputes : Computes inputEncoding Frame.wordEncoding initialWord :=
  recode (leftMapComputes Frame.wordEncoding RootBitmap.computes)
    (fun x => (x.val.1,ParentSearch.tailWord (graph x) (target x))) (fun _ => rfl)
    (fun x => by simpa only [pairEncoding_encode,Frame.wordEncoding,id_eq] using (initial_word x).symm)

@[simp] theorem rootComputes_machine : rootComputes.machine=rootMachine := rfl

theorem input_word (x : Input) : inputEncoding.encode x =
    Holant.Algebraic.frame (RootBitmap.inputEncoding.encode x.val.1)++ParentSearch.tailWord (graph x) (target x) := rfl

theorem initial_length_le (x : Input) : (initialWord x).length≤(inputEncoding.encode x).length := by
  simp only [initial_word,input_word,List.length_append,Holant.Algebraic.frame_length,
    RootBitmap.value_length,RootBitmap.input_word,List.length_replicate]
  omega

noncomputable def timePolynomial : Polynomial ℕ := rootComputes.time+2*(Polynomial.X+1)+ParentSearch.timePolynomial
noncomputable def timed (x : Input) :
    TM2OutputsInTime machine.computer (inputEncoding.encode x) (some (outputEncoding.encode (value x)))
      (timePolynomial.eval (inputEncoding.encode x).length) := by
  have h := Machine.compose_correct rootMachine (ParentSearch.machine ParentSearch.actual)
    (inputEncoding.encode x) (initialWord x) (outputEncoding.encode (value x))
    (rootComputes.time.eval (inputEncoding.encode x).length) (ParentSearch.timePolynomial.eval (initialWord x).length)
    (rootComputes.outputs x) (ParentSearch.timed (graph x) (root x) (vertex x))
  refine {steps := h.steps, evals_in_steps := h.evals_in_steps, steps_le_m := ?_}
  have hs := initial_length_le x
  have ht := natPolynomial_eval_mono ParentSearch.timePolynomial hs
  have hp := h.steps_le_m
  simp only [timePolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_one]
  omega

noncomputable def computes : Computes inputEncoding outputEncoding value where
  machine := machine
  time := timePolynomial
  outputs := timed

theorem inFP : InFP inputEncoding outputEncoding value := computes.inFP
noncomputable def primitivePolynomial : Polynomial ℕ := timePolynomial*Polynomial.C machine.primitiveBudget
theorem primitive_bound (x : Input) :
    primitiveCost machine (timed x).steps (some (initList machine.computer (inputEncoding.encode x))) ≤
      primitivePolynomial.eval (inputEncoding.encode x).length := by
  have h := Nat.mul_le_mul_right machine.primitiveBudget (timed x).steps_le_m
  simpa only [primitivePolynomial,Polynomial.eval_mul,Polynomial.eval_C] using le_trans (primitiveCost_le _ _ _) h

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RootedNonroot
