import Holant.Proofs.LinearProgramming.Support.MachineCombinators
import Holant.Proofs.LinearProgramming.Recovery.ExactPointRecovery.Bounds
import Holant.Proofs.LinearProgramming.Recovery.ExactPointRecovery.Semantics

set_option autoImplicit false

/-! Kernel-checked recovery component. Ported into the exclusive task namespace and validated with the pinned toolchain.
Sole entrypoint of this batch. An original n>=2 coordinate query physically
returns the original CounterLoop receipt together with the dyadic interval
produced by actual emitted-threshold receipt bits. False certifies original
Codec.Response.none; true isolates one bounded-denominator coordinate minimum.
This layer emits the certified interval and receipt. RationalExtraction.Source
and SuccessiveFaceMachine.Source supply scalar and common-face point recovery.
-/
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.ExactPointRecovery
open Holant.LocalDrafts.TraversalCompletion.RationalLP
open Holant.LocalDrafts.RemoteWork.RationalLP.Foundation
open Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators
open Turing Computability Holant.Algebraic Holant.Complexity BinaryCompose
open FixedFieldMachines GraphPreprocessing Codec
namespace Source
noncomputable section

attribute [local irreducible] prepare Native.machine

private def prepared_output {A B : Type} {ea : Encoding A Bool} {eb : Encoding B Bool}
    {f : A → B} (M : Computes ea eb f) (N : Machine) (g : A → B) (W T : Polynomial ℕ)
    (receipt : ∀ a, TM2OutputsInTime N.computer (eb.encode (f a))
      (some (eb.encode (g a))) (T.eval (ea.encode a).length))
    (width : ∀ a, (eb.encode (f a)).length≤W.eval (ea.encode a).length) (a : A) :
    TM2OutputsInTime (M.machine.compose N).computer (ea.encode a) (some (eb.encode (g a)))
      ((M.time+2*(W+1)+T).eval (ea.encode a).length) := by
  let o := Machine.compose_correct M.machine N (ea.encode a) (eb.encode (f a)) (eb.encode (g a))
    (M.time.eval (ea.encode a).length) (T.eval (ea.encode a).length) (M.outputs a) (receipt a)
  refine {steps := o.steps,evals_in_steps := o.evals_in_steps,steps_le_m := o.steps_le_m.trans ?_}
  have hw := width a
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_one]
  omega

def stateMachine : Machine := prepare.machine.compose Native.machine
def stateTime : Polynomial ℕ := prepare.time+2*(Bounds.width+1)+Bounds.loopTime
def stateOutput (c : CoordinateQuery) : TM2OutputsInTime stateMachine.computer (coordinateEncoding.encode c)
    (some (encoding.encode (resultState c))) (stateTime.eval (coordinateEncoding.encode c).length) := by
  dsimp only [stateMachine,stateTime]
  exact prepared_output prepare Native.machine resultState Bounds.width Bounds.loopTime
    Bounds.outputs Bounds.initial_length c
def stateComputes : Computes coordinateEncoding encoding resultState where
  machine := stateMachine
  time := stateTime
  outputs := stateOutput
def intervalPayloadComputes : Computes coordinateEncoding payloadEncoding
    (fun c : CoordinateQuery => payload (resultState c)) := stateComputes.andThen payloadComputes

/-- Only the legitimate n>=2 original-input scope is additional proof data.
It has exactly the existing original coordinate-query bytes. -/
abbrev HighCoordinate := {c : CoordinateQuery // 2≤c.1.val.dimension}
def highEncoding : Encoding HighCoordinate Bool where
  encode c := coordinateEncoding.encode c.val
  decode bits := do
    let c ← coordinateEncoding.decode bits
    if h : 2≤c.1.val.dimension then some ⟨c,h⟩ else none
  decode_encode c := by simp [c.property]
@[simp] theorem original_bytes (c : HighCoordinate) : highEncoding.encode c=coordinateEncoding.encode c.val := rfl
def originalInputComputes : Computes highEncoding Holant.LocalDrafts.RemoteWork.RationalLP.Complexity.CounterLoop.Source.highEncoding
    (fun c : HighCoordinate => ⟨c.val.1,c.property⟩) :=
  recode ThresholdProgram.coordinateInput (fun c => c.val) (fun _ => rfl) (fun _ => rfl)
def originalReceiptComputes : Computes highEncoding Holant.LocalDrafts.RemoteWork.RationalLP.Complexity.CounterLoop.Receipt.encoding
    (fun c : HighCoordinate => Holant.LocalDrafts.RemoteWork.RationalLP.Complexity.CounterLoop.Receipt.value c.val.1) :=
  originalInputComputes.andThen Holant.LocalDrafts.RemoteWork.RationalLP.Complexity.CounterLoop.Receipt.computes
def highIntervalComputes : Computes highEncoding payloadEncoding
    (fun c : HighCoordinate => payload (resultState c.val)) :=
  recode intervalPayloadComputes Subtype.val (fun _ => rfl) (fun _ => rfl)

abbrev Data := Holant.LocalDrafts.RemoteWork.RationalLP.Complexity.CounterLoop.Receipt.Data × Payload
def dataEncoding := pairEncoding Holant.LocalDrafts.RemoteWork.RationalLP.Complexity.CounterLoop.Receipt.encoding payloadEncoding
def value (c : HighCoordinate) : Data := (Holant.LocalDrafts.RemoteWork.RationalLP.Complexity.CounterLoop.Receipt.value c.val.1,payload (resultState c.val))
def computes : Computes highEncoding dataEncoding value := pairComputes originalReceiptComputes highIntervalComputes
def machine : Machine := computes.machine
def time : Polynomial ℕ := computes.time
private theorem computes_machine_eq : computes.machine=machine := rfl
def output (d : Input) (hn : 2≤d.val.dimension) (j : Fin d.val.dimension) :
    TM2OutputsInTime machine.computer (coordinateEncoding.encode ⟨d,j⟩)
      (some (dataEncoding.encode (value ⟨⟨d,j⟩,hn⟩)))
      (time.eval (coordinateEncoding.encode ⟨d,j⟩).length) := computes.outputs ⟨⟨d,j⟩,hn⟩

theorem original_lp (c : HighCoordinate) : (value c).1.2.1=c.val.1 :=
  Holant.LocalDrafts.RemoteWork.RationalLP.Complexity.CounterLoop.Receipt.original ⟨c.val.1,c.property⟩
theorem original_coordinate (c : HighCoordinate) : coordinate (value c).2=c.val :=
  Semantics.source_preserved c.val
theorem accepted (c : HighCoordinate) : (value c).1.1=true ↔ ∃ x, Feasible c.val.1.val x :=
  Holant.LocalDrafts.RemoteWork.RationalLP.Complexity.CounterLoop.Receipt.accepted ⟨c.val.1,c.property⟩
theorem rejected (c : HighCoordinate) : (value c).1.1=false ↔ ¬∃ x, Feasible c.val.1.val x :=
  Holant.LocalDrafts.RemoteWork.RationalLP.Complexity.CounterLoop.Receipt.rejected ⟨c.val.1,c.property⟩
theorem rejected_response (c : HighCoordinate) (ha : (value c).1.1=false) :
    Response c.val.1.val none := (rejected c).mp ha
theorem returned_center_thickened (c : HighCoordinate) (ha : (value c).1.1=true) :
    Holant.LocalDrafts.RemoteWork.RationalLP.Optimization.Thickening.At c.val.1.val (Holant.LocalDrafts.RemoteWork.RationalLP.Optimization.Thickening.epsilon c.val.1.val)
      (Codec.point c.val.1.val (value c).1.2.2.1) :=
  Holant.LocalDrafts.RemoteWork.RationalLP.Complexity.CounterLoop.Receipt.thickened c.val.1 c.property ha
theorem final_denominator (c : HighCoordinate) :
    denominator (value c).2=2^Denominator.rounds c.val.1.val := by
  simp [value,result_exact,payload,stamp]
theorem final_width (c : HighCoordinate) :
    (interval (value c).2).2-(interval (value c).2).1=
      (1:ℚ)/(2^Denominator.rounds c.val.1.val:ℕ) := by
  simpa [value,result_exact,payload,stamp] using Semantics.width c.val (Denominator.rounds c.val.1.val)

/-- The t here is a mathematical scalar isolation statement, not any field
of value c. No existential witness enters computes or its output word. -/
theorem successful_interval (c : HighCoordinate) (ha : (value c).1.1=true) :
    ∃ t : ℚ, Semantics.IsMinimum c.val t ∧ t.den≤InputBounds.denominator c.val.1.val ∧
      (interval (value c).2).1≤t ∧ t≤(interval (value c).2).2 ∧
      ∀ a : ℚ, a.den≤InputBounds.denominator c.val.1.val →
        (interval (value c).2).1≤a → a≤(interval (value c).2).2 → a=t :=
  Semantics.terminal_isolates c.val ((accepted c).mp ha)

theorem execution (c : HighCoordinate) : Holant.Complexity.StackProtocol.RunsExactly machine.computer.step
    (initList machine.computer (highEncoding.encode c))
    (haltList machine.computer (dataEncoding.encode (value c))) (computes.outputs c).steps :=
  (computes.outputs c).evals_in_steps
theorem output_bound (c : HighCoordinate) : (dataEncoding.encode (value c)).length≤
    computes.outputBound.bound.eval (highEncoding.encode c).length := computes.outputBound.length_le c
def primitivePolynomial : Polynomial ℕ := FixedFieldMachines.primitivePolynomial computes
def temporaryPolynomial : Polynomial ℕ := Polynomial.X+primitivePolynomial
theorem primitive_cost (c : HighCoordinate) :
    primitiveCost machine (computes.outputs c).steps (some (initList machine.computer (highEncoding.encode c)))≤
      primitivePolynomial.eval (highEncoding.encode c).length := computes_primitive_cost computes c
theorem temporary_bits (q : HighCoordinate) (t : ℕ) (ht : t≤(computes.outputs q).steps)
    (c : machine.Config)
    (hc : (fun p => p.bind machine.computer.step)^[t]
      (some (initList machine.computer (highEncoding.encode q)))=some c) :
    stackSize c.stk≤temporaryPolynomial.eval (highEncoding.encode q).length := by
  have hs := machine.run_size_le _ c t hc
  rw [machine.size_init] at hs
  apply hs.trans
  simpa only [temporaryPolynomial,primitivePolynomial,computes_machine_eq,Polynomial.eval_add,Polynomial.eval_X,
    FixedFieldMachines.primitivePolynomial,Polynomial.eval_mul,Polynomial.eval_C] using Nat.add_le_add_left
      (Nat.mul_le_mul_right machine.primitiveBudget (ht.trans (computes.outputs q).steps_le_m)) _

/-- Even a coordinate query's total cost is polynomial in original Input
bytes: its only extra data is the original j<n unary index. -/
def coordinateWidth : Polynomial ℕ := 3*Polynomial.X+1
theorem coordinate_length (c : CoordinateQuery) : (coordinateEncoding.encode c).length≤
    coordinateWidth.eval (inputEncoding.encode c.1).length := by
  have hn := InputBounds.dimension_le c.1.val
  have hj := c.2.isLt
  simp only [coordinateEncoding,Holant.OneHot.StackProgram.GraphLabelEncoding.sigmaEncoding_length,OccurrenceLabel.unaryPortEncoding,List.length_replicate]
  simp only [coordinateWidth,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,
    Polynomial.eval_X,Polynomial.eval_one]
  change c.1.val.dimension≤(inputEncoding.encode c.1).length at hn
  omega
def originalTime : Polynomial ℕ := time.comp coordinateWidth
def originalPrimitive : Polynomial ℕ := primitivePolynomial.comp coordinateWidth
def originalTemporary : Polynomial ℕ := temporaryPolynomial.comp coordinateWidth
def originalOutputWidth : Polynomial ℕ := computes.outputBound.bound.comp coordinateWidth
theorem original_time_bound (c : HighCoordinate) : (computes.outputs c).steps≤
    originalTime.eval (inputEncoding.encode c.val.1).length := by
  apply (computes.outputs c).steps_le_m.trans
  rw [originalTime,Polynomial.eval_comp]
  exact natPolynomial_eval_mono time (coordinate_length c.val)
theorem original_primitive_bound (c : HighCoordinate) :
    primitiveCost machine (computes.outputs c).steps (some (initList machine.computer (highEncoding.encode c)))≤
      originalPrimitive.eval (inputEncoding.encode c.val.1).length := by
  apply (primitive_cost c).trans
  rw [originalPrimitive,Polynomial.eval_comp]
  exact natPolynomial_eval_mono primitivePolynomial (coordinate_length c.val)
theorem original_output_bound (c : HighCoordinate) : (dataEncoding.encode (value c)).length≤
    originalOutputWidth.eval (inputEncoding.encode c.val.1).length := by
  apply (output_bound c).trans
  rw [originalOutputWidth,Polynomial.eval_comp]
  exact natPolynomial_eval_mono computes.outputBound.bound (coordinate_length c.val)
theorem original_temporary_bound (q : HighCoordinate) (t : ℕ) (ht : t≤(computes.outputs q).steps)
    (c : machine.Config)
    (hc : (fun p => p.bind machine.computer.step)^[t]
      (some (initList machine.computer (highEncoding.encode q)))=some c) :
    stackSize c.stk≤originalTemporary.eval (inputEncoding.encode q.val.1).length := by
  apply (temporary_bits q t ht c hc).trans
  rw [originalTemporary,Polynomial.eval_comp]
  exact natPolynomial_eval_mono temporaryPolynomial (coordinate_length q.val)

end
end Source
end Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.ExactPointRecovery
