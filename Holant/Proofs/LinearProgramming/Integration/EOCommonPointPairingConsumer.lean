import Holant.Proofs.LinearProgramming.Integration.EOCommonPointSource
import Holant.Proofs.Tractability.EOEvaluation.CandidateExecution.Backend
import Holant.Proofs.Algorithms.OptionalValue
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.OptionContextInterface
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.OptionMapInterface


namespace Holant.LocalDrafts.RemoteWork.RationalLP.Integration.EOCommonPointPairingConsumer
open Turing Computability Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines StackProtocol GraphPreprocessing
open GraphPreprocessing.OriginalCoefficient
open Holant.LocalDrafts.Tractability.AffineMachine
open Holant.LocalDrafts.TraversalCompletion.RationalLP
open Holant.LocalDrafts.Tractability
open Holant.LocalDrafts.Tractability.EOEvaluation
open Holant.OneHot.StackProgram.GraphLabelEncoding (optionEncoding)
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
noncomputable section
variable {s : ℕ} {arity : ℕ → ℕ}

abbrev Input := EOEvaluation.Source.Input (s := s) (arity := arity)
abbrev Output := CandidateExecution.Graph.Output (s := s) (arity := arity)
abbrev Result := Option (Option (Output (s := s) (arity := arity)))
def inputEncoding := EOEvaluation.Source.inputEncoding (s := s) (arity := arity)
def resultEncoding := optionEncoding (optionEncoding
  (CandidateExecution.Graph.outputEncoding (s := s) (arity := arity)))

private def payloadInputEncoding := pairEncoding
  (inputEncoding (s := s) (arity := arity)) EOCommonPointSource.payloadEncoding

/-- Read the returned mask suffix; the returned point and addressed table are
physically parsed/copied by these original projections, not host operations. -/
private def maskInput : Computes payloadInputEncoding CandidateExecution.Responses.inputEncoding
    (fun q : Input (s := s) (arity := arity) × EOCommonPointSource.Payload => (q.1,q.2.2.2)) := by
  let original := Wiring.firstComputes (inputEncoding (s := s) (arity := arity)) EOCommonPointSource.payloadEncoding
  let returned := Wiring.secondComputes (inputEncoding (s := s) (arity := arity)) EOCommonPointSource.payloadEncoding
  let tail := returned.andThen (Wiring.secondComputes Codec.pointEncoding
    (pairEncoding EOCommonPointSource.weightTableEncoding EOCommonPointSource.maskEncoding))
  let mask := tail.andThen (Wiring.secondComputes
    EOCommonPointSource.weightTableEncoding EOCommonPointSource.maskEncoding)
  exact pairComputes original mask

/-- This IS the old whole graph compiler. Its cell programme calls the old
maskComputes, PairingTemplates.computes and catalogue selector for each vertex. -/
private def paired : Computes payloadInputEncoding CandidateExecution.Graph.outputEncoding
    (fun q : Input (s := s) (arity := arity) × EOCommonPointSource.Payload =>
      CandidateExecution.Graph.value (q.1,q.2.2.2)) :=
  maskInput.andThen CandidateExecution.Graph.computes

private def innerInputEncoding := pairEncoding
  (inputEncoding (s := s) (arity := arity)) (optionEncoding EOCommonPointSource.payloadEncoding)
private def inner : Computes innerInputEncoding
    (optionEncoding (CandidateExecution.Graph.outputEncoding (s := s) (arity := arity)))
    (fun q : Input (s := s) (arity := arity) × Option EOCommonPointSource.Payload =>
      q.2.map (fun y => CandidateExecution.Graph.value (q.1,y.2.2))) :=
  congrComputes ((OptionContext.computes inputEncoding EOCommonPointSource.payloadEncoding).andThen
    (OptionMap.computes paired)) (fun q => by rcases q with ⟨r, p⟩; cases p <;> rfl)

private def contextEncoding := pairEncoding
  (inputEncoding (s := s) (arity := arity)) EOCommonPointSource.outputEncoding
private def consume : Computes contextEncoding resultEncoding
    (fun q : Input (s := s) (arity := arity) × EOCommonPointSource.Result =>
      q.2.map (Option.map (fun y => CandidateExecution.Graph.value (q.1,y.2.2)))) :=
  congrComputes ((OptionContext.computes inputEncoding
    (optionEncoding EOCommonPointSource.payloadEncoding)).andThen (OptionMap.computes inner))
      (fun q => by rcases q with ⟨r, p⟩; cases p <;> rfl)

def result (D : EOEvaluation.Source.Family s arity) (r : Input (s := s) (arity := arity)) :
    Result (s := s) (arity := arity) :=
  (EOCommonPointSource.value D r).map
    (Option.map (fun y => CandidateExecution.Graph.value (r,y.2.2)))

private def prepare (D : EOEvaluation.Source.Family s arity) :
    Computes inputEncoding contextEncoding (fun r => (r,EOCommonPointSource.value D r)) :=
  pairComputes (identityComputes inputEncoding) (EOCommonPointSource.Source.computes D)
def resultComputes (D : EOEvaluation.Source.Family s arity) :
    Computes inputEncoding resultEncoding (result D) := (prepare D).andThen consume

variable (D : EOEvaluation.Source.Family s arity)

/-- A specification of the ACTUAL returned mask, after its physical producer.
The old candidate programme is not invoked a second time. -/
theorem returned_mask (r : Input (s := s) (arity := arity)) (y : EOCommonPointSource.Payload)
    (hy : EOCommonPointSource.value D r=some (some y)) :
    y.2.2=CandidateExecution.Responses.truth D r :=
  EOCommonPointSource.mask_original D r y hy

theorem returned_mask_valid (r : Input (s := s) (arity := arity)) (y : EOCommonPointSource.Payload)
    (hy : EOCommonPointSource.value D r=some (some y)) :
    CandidateExecution.Responses.valid (r,y.2.2)=true := by
  rw [returned_mask D r y hy]
  exact CandidateExecution.Responses.truth_valid D r

theorem returned_addresses (r : Input (s := s) (arity := arity)) (y : EOCommonPointSource.Payload)
    (hy : EOCommonPointSource.value D r=some (some y)) :
    y=EOCommonPointSource.payload r y.1 ∧ y.2.1.length=(MatrixCompiler.raw D r).dimension ∧
      ∀ j : Fin (MatrixCompiler.raw D r).dimension,
        y.2.1.getD j.val (EOCommonPointSource.defaultColumn,0)=
          (ColumnOrder.encode r (ColumnOrder.order r j),
            EOCommonPointSource.weights D r y.1 (ColumnOrder.order r j).1 (ColumnOrder.order r j).2) :=
  EOCommonPointSource.addressed_output D r y hy

theorem local_mask (r : Input (s := s) (arity := arity)) (y : EOCommonPointSource.Payload)
    (hy : EOCommonPointSource.value D r=some (some y)) (v : Fin r.val.vertices.length) :
    CandidateExecution.Responses.mask (arity (r.val.vertices.get v).1)
      ((r,y.2.2),v.val,r.val.vertices.get v)=CandidatePairing.mask D r v := by
  rw [returned_mask D r y hy]
  exact CandidateExecution.Responses.mask_truth D r v

theorem local_good (r : Input (s := s) (arity := arity)) (y : EOCommonPointSource.Payload)
    (hy : EOCommonPointSource.value D r=some (some y)) (v : Fin r.val.vertices.length) :
    PairingTemplates.Good (CandidateExecution.Responses.mask (arity (r.val.vertices.get v).1)
      ((r,y.2.2),v.val,r.val.vertices.get v)) := by
  rw [local_mask D r y hy]
  exact CandidatePairing.good D r v

theorem selected (r : Input (s := s) (arity := arity)) (y : EOCommonPointSource.Payload)
    (hy : EOCommonPointSource.value D r=some (some y)) (v : Fin r.val.vertices.length) :
    CandidateExecution.Records.candidate ((r,y.2.2),v.val,r.val.vertices.get v)
      (r.val.signatureLabel r.property v)=
        ⟨r.val.signatureLabel r.property v,some (CandidatePairing.label D r v)⟩ := by
  rw [returned_mask D r y hy]
  exact CandidateExecution.Records.true_candidate D r v

theorem selected_covers (r : Input (s := s) (arity := arity)) (y : EOCommonPointSource.Payload)
    (hy : EOCommonPointSource.value D r=some (some y)) (v : Fin r.val.vertices.length) :
    PairingTemplates.select (CandidateExecution.Responses.mask (arity (r.val.vertices.get v).1)
      ((r,y.2.2),v.val,r.val.vertices.get v))=some (CandidatePairing.label D r v) ∧
      PairingTemplates.Covers (CandidateExecution.Responses.mask (arity (r.val.vertices.get v).1)
        ((r,y.2.2),v.val,r.val.vertices.get v)) (PairingTemplates.decode (CandidatePairing.label D r v)) := by
  rw [local_mask D r y hy]
  exact CandidatePairing.label_spec D r v

theorem literal_ports (r : Input (s := s) (arity := arity)) (y : EOCommonPointSource.Payload)
    (v : Fin r.val.vertices.length) :
    ((CandidateExecution.Graph.raw (r,y.2.2)).vertices.get
      (CandidateExecution.Graph.vertexIndex (r,y.2.2) v)).2=(r.val.vertices.get v).2 := by
  rw [CandidateExecution.Graph.vertex_get]
  rfl

theorem original_label (r : Input (s := s) (arity := arity)) (y : EOCommonPointSource.Payload)
    (hy : EOCommonPointSource.value D r=some (some y)) (v : Fin r.val.vertices.length) :
    (CandidateExecution.Graph.raw (r,y.2.2)).signatureLabel
      (CandidateExecution.Graph.wellFormed (r,y.2.2)) (CandidateExecution.Graph.vertexIndex (r,y.2.2) v)=
      CandidateExecution.Catalogue.codes
        ⟨r.val.signatureLabel r.property v,some (CandidatePairing.label D r v)⟩ := by
  rw [CandidateExecution.Semantics.vertex_label]
  change CandidateExecution.Catalogue.codes
    (CandidateExecution.Records.candidate ((r,y.2.2),v.val,r.val.vertices.get v)
      (r.val.signatureLabel r.property v))=_
  rw [selected D r y hy v]

theorem paired_denote (r : Input (s := s) (arity := arity)) (y : EOCommonPointSource.Payload)
    (hy : EOCommonPointSource.value D r=some (some y)) :
    (CandidateExecution.Semantics.target D (r,y.2.2)).denote Fin.elim0=
      (EOEvaluation.Source.network D r).denote Fin.elim0 := by
  rw [returned_mask D r y hy]
  exact CandidateExecution.Semantics.true_denote D r

theorem result_origin (r : Input (s := s) (arity := arity)) (g : Output (s := s) (arity := arity))
    (hg : result D r=some (some g)) :
    ∃ y, EOCommonPointSource.value D r=some (some y) ∧
      g=CandidateExecution.Graph.value (r,y.2.2) := by
  unfold result at hg
  obtain ⟨p,hp,hg⟩ := Option.map_eq_some_iff.mp hg
  obtain ⟨y,hy,he⟩ := Option.map_eq_some_iff.mp hg
  exact ⟨y,by simpa only [hy] using hp,he.symm⟩

theorem result_not_malformed (r : Input (s := s) (arity := arity)) : result D r≠none := by
  intro h
  exact EOCommonPointSource.not_malformed D r (Option.map_eq_none_iff.mp h)

theorem result_negative (r : Input (s := s) (arity := arity)) : result D r=some none ↔
    ¬∃ w, Relaxation.Feasible (EOEvaluation.Source.network D r) w := by
  have hm : result D r=some none ↔ EOCommonPointSource.value D r=some none := by
    cases h : EOCommonPointSource.value D r with
    | none => simp [result,h]
    | some p => cases p <;> simp [result,h]
  exact hm.trans (EOCommonPointSource.infeasible_original_iff D r)

theorem negative_zero (r : Input (s := s) (arity := arity)) (h : result D r=some none) :
    (EOEvaluation.Source.network D r).denote Fin.elim0=0 :=
  EOEvaluation.Source.infeasible_value D r ((result_negative D r).mp h)

theorem graph_preserved (r : Input (s := s) (arity := arity)) (g : Output (s := s) (arity := arity))
    (hg : result D r=some (some g)) :
    g.val.vertices.length=r.val.vertices.length ∧ g.val.edges=r.val.edges ∧
      g.val.endpoints=r.val.endpoints := by
  obtain ⟨y,hy,rfl⟩ := result_origin D r g hg
  exact ⟨CandidateExecution.Graph.vertices_length (r,y.2.2),rfl,
    CandidateExecution.Graph.endpoints (r,y.2.2)⟩

/-- The existing A/P backend consumes precisely the physically selected graph,
and already recovers the original D coefficient field, including native X. -/
theorem backend_original (r : Input (s := s) (arity := arity)) (y : EOCommonPointSource.Payload)
    (hy : EOCommonPointSource.value D r=some (some y)) :
    CandidateExecution.Backend.recovered D (CandidateExecution.Graph.value (r,y.2.2))=
      CandidateExecution.Backend.sourceValue D r := by
  rw [returned_mask D r y hy]
  exact CandidateExecution.Backend.true_value D r

abbrev presentation := CandidateExecution.Backend.sourcePresentation D
abbrev originalValue := CandidateExecution.Backend.sourceValue D
def returnedValueEncoding := optionEncoding (optionEncoding (presentation D).encoding)
def returnedValue (r : Input (s := s) (arity := arity)) :=
  (result D r).map (Option.map (CandidateExecution.Backend.recovered D))
private def returnedComputes : Computes inputEncoding (returnedValueEncoding D) (returnedValue D) :=
  (resultComputes D).andThen
    (OptionMap.computes (OptionMap.computes (CandidateExecution.Backend.computes D)))
def value (r : Input (s := s) (arity := arity)) := ((returnedValue D r).getD none).getD 0
private def evaluator : Computes inputEncoding (presentation D).encoding (value D) :=
  (returnedComputes D).andThen
    ((Holant.LocalDrafts.MainChain.OptionalValue.getDComputes (optionEncoding (presentation D).encoding) none).andThen
      (Holant.LocalDrafts.MainChain.OptionalValue.getDComputes (presentation D).encoding 0))

theorem original_zero (r : Input (s := s) (arity := arity)) (h : result D r=some none) :
    originalValue D r=0 := by
  apply Subtype.ext
  change (CandidateExecution.Backend.sourceValue D r : AlgebraicComplex)=0
  exact (Holant.LocalDrafts.MainChain.OriginalFamily.value_exact
    D.signatures CandidateExecution.Catalogue.kernels r).trans (negative_zero D r h)

theorem value_exact (r : Input (s := s) (arity := arity)) : value D r=originalValue D r := by
  cases h : EOCommonPointSource.value D r with
  | none => exact False.elim (EOCommonPointSource.not_malformed D r h)
  | some p =>
    cases p with
    | none =>
      have hn : result D r=some none := by simp only [result,h,Option.map_some,Option.map_none]
      simpa only [value,returnedValue,hn,Option.map_some,Option.map_none,Option.getD_some,
        Option.getD_none] using (original_zero D r hn).symm
    | some y =>
      simpa only [value,returnedValue,result,h,Option.map_some,Option.getD_some] using
        backend_original D r y h

/-- Two-way interpretation of the physically retained intermediate tags. -/
theorem returned_negative (r : Input (s := s) (arity := arity)) :
    returnedValue D r=some none ↔ ¬∃ w, Relaxation.Feasible (EOEvaluation.Source.network D r) w := by
  have hm : returnedValue D r=some none ↔ result D r=some none := by
    cases h : result D r with
    | none => simp [returnedValue,h]
    | some p => cases p <;> simp [returnedValue,h]
  exact hm.trans (result_negative D r)
theorem returned_not_malformed (r : Input (s := s) (arity := arity)) : returnedValue D r≠none := by
  intro h
  exact result_not_malformed D r (Option.map_eq_none_iff.mp h)

private theorem congr_machine {A B : Type} {ea : Encoding A Bool} {eb : Encoding B Bool}
    {f g : A → B} (w : Computes ea eb f) (h : ∀ a, f a=g a) :
    (congrComputes w h).machine=w.machine := rfl
private theorem congr_clock {A B : Type} {ea : Encoding A Bool} {eb : Encoding B Bool}
    {f g : A → B} (w : Computes ea eb f) (h : ∀ a, f a=g a) :
    (congrComputes w h).time=w.time := rfl

namespace Source

/-- Sole evaluator installation: original family and original validated graph
are the only inputs. Both semantic replacements preserve the literal machine. -/
def computes : Computes inputEncoding (presentation D).encoding (originalValue D) :=
  congrComputes (evaluator D) (value_exact D)
def machine : Machine := (computes D).machine
def time : Polynomial ℕ := (computes D).time
def primitivePolynomial : Polynomial ℕ := FixedFieldMachines.primitivePolynomial (computes D)
def storagePolynomial : Polynomial ℕ := Polynomial.X+primitivePolynomial D
theorem inFP : InFP inputEncoding (presentation D).encoding (originalValue D) := (computes D).inFP
theorem same_machine : (computes D).machine=(evaluator D).machine :=
  congr_machine (evaluator D) (value_exact D)
theorem same_clock : time D=(evaluator D).time := congr_clock (evaluator D) (value_exact D)

theorem execution (r : Input (s := s) (arity := arity)) :
    RawSource.RunsOn (machine D).computer.step (initList (machine D).computer (inputEncoding.encode r))
      (haltList (machine D).computer ((presentation D).encoding.encode (originalValue D r)))
      ((computes D).outputs r).steps := ((computes D).outputs r).evals_in_steps
theorem steps_bound (r : Input (s := s) (arity := arity)) :
    ((computes D).outputs r).steps≤(time D).eval (inputEncoding.encode r).length :=
  ((computes D).outputs r).steps_le_m
theorem primitive_bound (r : Input (s := s) (arity := arity)) :
    primitiveCost (machine D) ((computes D).outputs r).steps
      (some (initList (machine D).computer (inputEncoding.encode r)))≤
      (primitivePolynomial D).eval (inputEncoding.encode r).length := computes_primitive_cost (computes D) r
theorem output_bound (r : Input (s := s) (arity := arity)) :
    ((presentation D).encoding.encode (originalValue D r)).length≤
      (computes D).outputBound.bound.eval (inputEncoding.encode r).length := (computes D).outputBound.length_le r
theorem prefix_storage (r : Input (s := s) (arity := arity)) (t : ℕ)
    (ht : t≤((computes D).outputs r).steps) (c : (machine D).Config)
    (hc : (fun p => p.bind (machine D).computer.step)^[t]
      (some (initList (machine D).computer (inputEncoding.encode r)))=some c) :
    stackSize c.stk≤(storagePolynomial D).eval (inputEncoding.encode r).length := by
  have hs := (machine D).run_size_le _ c t hc
  rw [Machine.size_init] at hs
  have hb := Nat.mul_le_mul_right (machine D).primitiveBudget
    (ht.trans ((computes D).outputs r).steps_le_m)
  apply hs.trans
  simpa only [storagePolynomial,primitivePolynomial,FixedFieldMachines.primitivePolynomial,machine,time,
    Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C] using
      Nat.add_le_add_left hb (inputEncoding.encode r).length

/-- Actual returned graph bytes have exactly the old two failure tags. -/
theorem pairing_execution (r : Input (s := s) (arity := arity)) :
    RawSource.RunsOn (resultComputes D).machine.computer.step
      (initList (resultComputes D).machine.computer (inputEncoding.encode r))
      (haltList (resultComputes D).machine.computer (resultEncoding.encode (result D r)))
      ((resultComputes D).outputs r).steps := ((resultComputes D).outputs r).evals_in_steps
theorem pairing_result_run_iff (r : Input (s := s) (arity := arity))
    (out : Result (s := s) (arity := arity)) :
    (∃ steps, RawSource.RunsOn (resultComputes D).machine.computer.step
      (initList (resultComputes D).machine.computer (inputEncoding.encode r))
      (haltList (resultComputes D).machine.computer (resultEncoding.encode out)) steps) ↔ result D r=out := by
  constructor
  · rintro ⟨steps,hrun⟩
    apply resultEncoding.encode_injective
    exact ResidualExpansion.machine_output_unique (resultComputes D).machine _ _ _
      ((resultComputes D).outputs r).steps steps (pairing_execution D r) hrun
  · intro he
    exact ⟨((resultComputes D).outputs r).steps,by simpa only [he] using pairing_execution D r⟩
theorem negative_pairing_run_iff (r : Input (s := s) (arity := arity)) :
    (∃ steps, RawSource.RunsOn (resultComputes D).machine.computer.step
      (initList (resultComputes D).machine.computer (inputEncoding.encode r))
      (haltList (resultComputes D).machine.computer [true,false]) steps) ↔
        ¬∃ w, Relaxation.Feasible (EOEvaluation.Source.network D r) w :=
  (pairing_result_run_iff D r (some none)).trans (result_negative D r)
theorem no_malformed_pairing_run (r : Input (s := s) (arity := arity)) :
    ¬∃ steps, RawSource.RunsOn (resultComputes D).machine.computer.step
      (initList (resultComputes D).machine.computer (inputEncoding.encode r))
      (haltList (resultComputes D).machine.computer [false]) steps := by
  intro h
  exact result_not_malformed D r ((pairing_result_run_iff D r none).mp h)

theorem returned_execution (r : Input (s := s) (arity := arity)) :
    RawSource.RunsOn (returnedComputes D).machine.computer.step
      (initList (returnedComputes D).machine.computer (inputEncoding.encode r))
      (haltList (returnedComputes D).machine.computer ((returnedValueEncoding D).encode (returnedValue D r)))
      ((returnedComputes D).outputs r).steps := ((returnedComputes D).outputs r).evals_in_steps

theorem answer_ambient (r : Input (s := s) (arity := arity)) :
    (originalValue D r : AlgebraicComplex)=(EOEvaluation.Source.network D r).denote Fin.elim0 :=
  Holant.LocalDrafts.MainChain.OriginalFamily.value_exact D.signatures CandidateExecution.Catalogue.kernels r

/-- Any observed final clean word belongs to the OLD original-D answer
codec and is the value of THIS original graph. The observed execution is a
postcondition, not a point, pairing or halt-correctness source parameter.
-/
theorem observed_value (r : Input (s := s) (arity := arity)) (word : List Bool) (steps : ℕ)
    (hrun : RawSource.RunsOn (machine D).computer.step
      (initList (machine D).computer (inputEncoding.encode r))
      (haltList (machine D).computer word) steps) :
    word=(presentation D).encoding.encode (originalValue D r) ∧
    (presentation D).encoding.decode word=some (originalValue D r) ∧
    (originalValue D r : AlgebraicComplex)=(EOEvaluation.Source.network D r).denote Fin.elim0 ∧
    word.length≤(computes D).outputBound.bound.eval (inputEncoding.encode r).length := by
  have hw : word=(presentation D).encoding.encode (originalValue D r) :=
    ResidualExpansion.machine_output_unique (machine D) (inputEncoding.encode r) word
      ((presentation D).encoding.encode (originalValue D r))
      steps ((computes D).outputs r).steps hrun (execution D r)
  refine ⟨hw,?_,answer_ambient D r,?_⟩
  · rw [hw]
    exact (presentation D).encoding.decode_encode (originalValue D r)
  · rw [hw]
    exact output_bound D r

/-- A physically observed negative pairing tag makes the SAME final
programme emit the original-field zero at its existing charged step count.
This implication does not identify every zero Holant value as infeasible.
-/
theorem negative_pairing_zero (r : Input (s := s) (arity := arity)) (steps : ℕ)
    (hrun : RawSource.RunsOn (resultComputes D).machine.computer.step
      (initList (resultComputes D).machine.computer (inputEncoding.encode r))
      (haltList (resultComputes D).machine.computer [true,false]) steps) :
    (¬∃ w, Relaxation.Feasible (EOEvaluation.Source.network D r) w) ∧
    originalValue D r=0 ∧
    RawSource.RunsOn (machine D).computer.step
      (initList (machine D).computer (inputEncoding.encode r))
      (haltList (machine D).computer ((presentation D).encoding.encode 0))
      ((computes D).outputs r).steps := by
  have hword : resultEncoding.encode (some none : Result (s := s) (arity := arity))=[true,false] := rfl
  have hencoded : RawSource.RunsOn (resultComputes D).machine.computer.step
      (initList (resultComputes D).machine.computer (inputEncoding.encode r))
      (haltList (resultComputes D).machine.computer
        (resultEncoding.encode (some none : Result (s := s) (arity := arity)))) steps := by
    simpa only [hword] using hrun
  have hn := (pairing_result_run_iff D r (some none)).mp ⟨steps,hencoded⟩
  have hz := original_zero D r hn
  refine ⟨(result_negative D r).mp hn,hz,?_⟩
  simpa only [hz] using execution D r

/-- An observed successful graph comes from the actual common point return,
not from a supplied mask or chosen pairing. The weights are on the same
original coordinate order; the old backend recovers the original value.
-/
theorem pairing_point_run (r : Input (s := s) (arity := arity))
    (g : Output (s := s) (arity := arity)) (steps : ℕ)
    (hrun : RawSource.RunsOn (resultComputes D).machine.computer.step
      (initList (resultComputes D).machine.computer (inputEncoding.encode r))
      (haltList (resultComputes D).machine.computer
        (true::true::CandidateExecution.Graph.outputEncoding.encode g)) steps) :
    ∃ y, EOCommonPointSource.value D r=some (some y) ∧
      Codec.Solution (MatrixCompiler.raw D r) y.1 ∧
      Relaxation.Feasible (EOEvaluation.Source.network D r) (EOCommonPointSource.weights D r y.1) ∧
      (∀ c : EOEvaluation.Source.Coordinate r,
        0<EOCommonPointSource.weights D r y.1 c.1 c.2 ↔
          Relaxation.Candidate (EOEvaluation.Source.network D r) c.1 c.2) ∧
      y.2.2=CandidateExecution.Responses.truth D r ∧
      g=CandidateExecution.Graph.value (r,y.2.2) ∧
      CandidateExecution.Backend.recovered D g=originalValue D r := by
  have hword : resultEncoding.encode (some (some g))=
      true::true::CandidateExecution.Graph.outputEncoding.encode g := rfl
  have hencoded : RawSource.RunsOn (resultComputes D).machine.computer.step
      (initList (resultComputes D).machine.computer (inputEncoding.encode r))
      (haltList (resultComputes D).machine.computer (resultEncoding.encode (some (some g)))) steps := by
    simpa only [hword] using hrun
  have hg := (pairing_result_run_iff D r (some (some g))).mp ⟨steps,hencoded⟩
  obtain ⟨y,hy,he⟩ := result_origin D r g hg
  have hs := EOCommonPointSource.common_sound D r y hy
  refine ⟨y,hy,hs.1,hs.2.1,hs.2.2.1,returned_mask D r y hy,he,?_⟩
  rw [he]
  exact backend_original D r y hy

/-- Exact old original-D presentation, rather than a new field or answer codec. -/
theorem original_codec : (presentation D).encoding=
    (CandidateExecution.Backend.sourcePresentation D).encoding := rfl

/-- The original graph alone produces the run, both tag meanings, all original
addresses, covering labels and original-field answer. No branch is an input. -/
theorem top (r : Input (s := s) (arity := arity)) :
    RawSource.RunsOn (machine D).computer.step (initList (machine D).computer (inputEncoding.encode r))
      (haltList (machine D).computer ((presentation D).encoding.encode (originalValue D r)))
      ((computes D).outputs r).steps ∧
    ((computes D).outputs r).steps≤(time D).eval (inputEncoding.encode r).length ∧
    result D r≠none ∧
    (result D r=some none ↔ ¬∃ w, Relaxation.Feasible (EOEvaluation.Source.network D r) w) ∧
    (result D r=some none → originalValue D r=0) ∧
    (∀ g, result D r=some (some g) → ∃ y,
      EOCommonPointSource.value D r=some (some y) ∧ g=CandidateExecution.Graph.value (r,y.2.2) ∧
      y.2.2=CandidateExecution.Responses.truth D r ∧
      y=EOCommonPointSource.payload r y.1 ∧ y.2.1.length=(MatrixCompiler.raw D r).dimension ∧
      (∀ j : Fin (MatrixCompiler.raw D r).dimension,
        y.2.1.getD j.val (EOCommonPointSource.defaultColumn,0)=
          (ColumnOrder.encode r (ColumnOrder.order r j),
            EOCommonPointSource.weights D r y.1 (ColumnOrder.order r j).1 (ColumnOrder.order r j).2)) ∧
      g.val.vertices.length=r.val.vertices.length ∧ g.val.edges=r.val.edges ∧
      g.val.endpoints=r.val.endpoints ∧
      (∀ v : Fin r.val.vertices.length,
        PairingTemplates.select (CandidateExecution.Responses.mask (arity (r.val.vertices.get v).1)
          ((r,y.2.2),v.val,r.val.vertices.get v))=some (CandidatePairing.label D r v) ∧
        PairingTemplates.Covers (CandidateExecution.Responses.mask (arity (r.val.vertices.get v).1)
          ((r,y.2.2),v.val,r.val.vertices.get v)) (PairingTemplates.decode (CandidatePairing.label D r v))) ∧
      (CandidateExecution.Semantics.target D (r,y.2.2)).denote Fin.elim0=
        (EOEvaluation.Source.network D r).denote Fin.elim0) := by
  refine ⟨execution D r,steps_bound D r,result_not_malformed D r,result_negative D r,
    original_zero D r,?_⟩
  intro g hg
  obtain ⟨y,hy,he⟩ := result_origin D r g hg
  obtain ⟨hpayload,haddress,hcolumns⟩ := returned_addresses D r y hy
  obtain ⟨hv,hedges,hports⟩ := graph_preserved D r g hg
  exact ⟨y,hy,he,returned_mask D r y hy,hpayload,haddress,hcolumns,hv,hedges,hports,
    fun v => selected_covers D r y hy v,paired_denote D r y hy⟩

end Source
end
end Holant.LocalDrafts.RemoteWork.RationalLP.Integration.EOCommonPointPairingConsumer
