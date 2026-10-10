import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RootBitmapInterface
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.BitmapIterateInterface

/-! Actual root initialization followed by the actual V-round reachability
machine. The entry retains the original unary root and vertex count plus the
literal original endpoint table. No initial bitmap or size certificate is input. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RootReach
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
open Holant.OneHot.Computable
open Holant.OneHot.StackProgram.GraphLabelEncoding
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option synthInstance.maxSize 2048
set_option Elab.async false

abbrev Input := Σ root : RootBitmap.Input, List (Fin root.1 × Fin root.1)
def inputEncoding : Encoding Input Bool := sigmaEncoding RootBitmap.inputEncoding (fun root => NeighborScan.edgeEncoding root.1)
def graph (x : Input) : Graph := ⟨x.1.1,x.2⟩
def initialWord (x : Input) : List Bool := BitmapIterate.word (graph x) {x.1.2}
def value (x : Input) : List Bool := NeighborPredicate.bitmap (graph x) ((graph x).reach x.1.2 (graph x).vertices)

@[simp] theorem input_word (x : Input) :
    inputEncoding.encode x = Holant.Algebraic.frame (RootBitmap.inputEncoding.encode x.1)++NeighborScan.edgeBits x.2 := rfl

theorem initial_word (x : Input) :
    initialWord x = Holant.Algebraic.frame (RootBitmap.value x.1)++NeighborScan.edgeBits x.2 := by
  have h := RootBitmap.graph_value (graph x) x.1.2
  change RootBitmap.value x.1 = NeighborPredicate.bitmap (graph x) {x.1.2} at h
  unfold initialWord BitmapIterate.word
  rw [← h]
  rfl

abbrev rootMachine : Machine := LeftMap.machine RootBitmap.machine
abbrev machine : Machine := rootMachine.compose (BitmapIterate.machine BitmapIterate.roundMachine)

noncomputable def rootComputes : Computes inputEncoding Frame.wordEncoding initialWord :=
  recode (leftMapComputes Frame.wordEncoding RootBitmap.computes)
    (fun x => (x.1,NeighborScan.edgeBits x.2)) (fun _ => rfl)
    (fun x => by simpa only [pairEncoding_encode,Frame.wordEncoding,id_eq] using (initial_word x).symm)

@[simp] theorem rootComputes_machine : rootComputes.machine=rootMachine := rfl

theorem initial_length_le (x : Input) : (initialWord x).length≤(inputEncoding.encode x).length := by
  simp only [initial_word,input_word,List.length_append,Holant.Algebraic.frame_length,
    RootBitmap.value_length,RootBitmap.input_word,List.length_replicate]
  omega

noncomputable def timePolynomial : Polynomial ℕ := rootComputes.time+2*(Polynomial.X+1)+BitmapIterate.timePolynomial

/-- The composition includes the real framed-word transfer between initialization
and iteration, with its length bounded by the actual original entry bytes. -/
noncomputable def timed (x : Input) : TM2OutputsInTime machine.computer (inputEncoding.encode x) (some (value x))
    (timePolynomial.eval (inputEncoding.encode x).length) := by
  have h := Machine.compose_correct rootMachine (BitmapIterate.machine BitmapIterate.roundMachine)
    (inputEncoding.encode x) (initialWord x) (value x)
    (rootComputes.time.eval (inputEncoding.encode x).length) (BitmapIterate.timePolynomial.eval (initialWord x).length)
    (rootComputes.outputs x) (BitmapIterate.reach_timed (graph x) x.1.2)
  refine {steps := h.steps, evals_in_steps := h.evals_in_steps, steps_le_m := ?_}
  have hs := initial_length_le x
  have ht := natPolynomial_eval_mono BitmapIterate.timePolynomial hs
  have hp := h.steps_le_m
  simp only [timePolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_one]
  omega

noncomputable def computes : Computes inputEncoding Frame.wordEncoding value where
  machine := machine
  time := timePolynomial
  outputs := timed

theorem inFP : InFP inputEncoding Frame.wordEncoding value := computes.inFP

noncomputable def primitivePolynomial : Polynomial ℕ := timePolynomial*Polynomial.C machine.primitiveBudget
theorem primitive_bound (x : Input) :
    primitiveCost machine (timed x).steps (some (initList machine.computer (inputEncoding.encode x))) ≤
      primitivePolynomial.eval (inputEncoding.encode x).length := by
  have h := Nat.mul_le_mul_right machine.primitiveBudget (timed x).steps_le_m
  simpa only [primitivePolynomial,Polynomial.eval_mul,Polynomial.eval_C] using le_trans (primitiveCost_le _ _ _) h

@[simp] theorem value_length (x : Input) : (value x).length=x.1.1 := by simp [value,graph]

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RootReach
