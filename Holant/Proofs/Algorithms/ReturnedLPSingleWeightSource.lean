import Holant.Proofs.Tractability.EOEvaluation.SingleWeightSource.Fields
import Holant.Proofs.LinearProgramming.Integration.EOOriginalFamilySource
import Holant.Proofs.Algorithms.OptionalValue


namespace Holant.LocalDrafts.MainChain.ReturnedLPSingleWeightSource
open Turing Computability Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing.OriginalCoefficient
open Holant.LocalDrafts.Hardness
open Holant.OneHot.StackProgram.GraphLabelEncoding (optionEncoding)
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace P
export Holant.LocalDrafts.Tractability.EOEvaluation.SingleWeightSource.Producer
  (Input native layer layer_spec completedArity completedTable completed_positive_original
   count targetArity targetTable)
end P
namespace Fields
export Holant.LocalDrafts.Tractability.EOEvaluation.SingleWeightSource.Fields
  (completedCoefficient completedPresentation completedValue completedInclusion completedInclusionComputes)
end Fields
namespace EOF
export Holant.LocalDrafts.RemoteWork.RationalLP.Integration.EOOriginalFamilySource
  (presentation value computes answer_ambient count targetArity targetTable)
end EOF
namespace Raw
export Holant.LocalDrafts.RemoteWork.RationalLP.RawSource (RunsOn)
end Raw
namespace EO
export Holant.LocalDrafts.Tractability.EOEvaluation.Source (signatureSet)
end EO

variable {s : ℕ} {arity : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (arity i.val))
variable (Gamma : SignatureFamily AlgebraicComplex)
variable (hmem : ∀i,(⟨arity i.val,G i⟩ : AnySignature AlgebraicComplex)∈Gamma)
variable (h : SingleWeightAlternative (preprocess Gamma))

abbrev Input := P.Input (s:=s) (arity:=arity)
abbrev inputEncoding := KSourceTransport.inputEncoding (s:=s) (arity:=arity)
abbrev presentation := KSourceTransport.originalPresentation G
abbrev value := KSourceTransport.originalValue G
abbrev CompletedInput := ExactSignatureTables.Input s 1 (P.completedArity G Gamma hmem h)

/-- Each retained completed signature comes from its SAME original label,
native K-inverse tensor and internally selected single layer. Both charge
signs are allowed; no new common-side or EO promise is introduced. -/
theorem completed_subset : preprocess (EO.signatureSet (P.completedTable G Gamma hmem h)) ⊆
    completionFamily (kCoordinates (preprocess Gamma)) := by
  rintro f ⟨⟨i,rfl⟩,hp,hn⟩
  have hnative : P.native G i≠0 :=
    (SingleWeightCompletion.table_nonzero (P.native G) (P.layer G Gamma hmem h) i).mp hn
  have hm : SingleWeightCompletion.label (P.native G) (P.layer G Gamma hmem h) i ∈
      completionFamily (kCoordinates (preprocess Gamma)) :=
    ⟨⟨arity i.val,P.native G i⟩,
      Holant.LocalDrafts.Tractability.EOEvaluation.OneSidedSource.Producer.native_member
        G Gamma hmem i (P.completed_positive_original G Gamma hmem h i hp)
        (Holant.LocalDrafts.Tractability.EOEvaluation.OneSidedSource.Producer.native_nonzero_original
          G i hnative),
      hnative,P.layer G Gamma hmem h i,P.layer_spec G Gamma hmem h i,rfl⟩
  exact (congrArg (fun f : AnySignature AlgebraicComplex =>
    f ∈ completionFamily (kCoordinates (preprocess Gamma)))
      (SingleWeightCompletion.table_label (P.native G) (P.layer G Gamma hmem h) i)).mpr hm

def eoCondition : EOTract (preprocess (EO.signatureSet (P.completedTable G Gamma hmem h))) :=
  h.2.2.mono_family (completed_subset G Gamma hmem h)

theorem same_retained_count : EOF.count (P.completedTable G Gamma hmem h)=P.count G Gamma hmem h := rfl
theorem same_retained_arity : EOF.targetArity (P.completedTable G Gamma hmem h)=P.targetArity G Gamma hmem h := rfl
theorem same_retained_table : EOF.targetTable (P.completedTable G Gamma hmem h)=P.targetTable G Gamma hmem h := rfl

private abbrev returnedCoefficient := RootPreprocessing.sourceCoefficient (P.completedTable G Gamma hmem h)

/-- The new endpoint's B+X presentation is transported by an actual fixed
rational matrix to the prescribed completed codec. Ambient equality proves
its retraction law without identifying either chosen basis or byteword. -/
private def returnedToCompleted : Computes
    (EOF.presentation (P.completedTable G Gamma hmem h)).encoding
    (Fields.completedPresentation G Gamma hmem h).encoding
    (FamilyAnswerTransport.recover (Fields.completedCoefficient G Gamma hmem h)
      (returnedCoefficient G Gamma hmem h)) :=
  FamilyAnswerTransport.computes (Fields.completedCoefficient G Gamma hmem h)
    (returnedCoefficient G Gamma hmem h)
    (OriginalFamily.coefficient_algebraic (P.completedTable G Gamma hmem h) KSourceTransport.nativeEdges)
    (OriginalFamily.coefficient_algebraic (P.completedTable G Gamma hmem h) RootPreprocessing.nativeX)

private theorem returned_recovery (r : CompletedInput G Gamma hmem h) :
    FamilyAnswerTransport.recover (Fields.completedCoefficient G Gamma hmem h)
      (returnedCoefficient G Gamma hmem h) (EOF.value (P.completedTable G Gamma hmem h) r)=
      Fields.completedValue G Gamma hmem h r := by
  apply FamilyAnswerTransport.recover_exact (Fields.completedCoefficient G Gamma hmem h)
    (returnedCoefficient G Gamma hmem h) (Fields.completedValue G Gamma hmem h r)
    (EOF.value (P.completedTable G Gamma hmem h) r)
  exact (EOF.answer_ambient (P.completedTable G Gamma hmem h) r).trans
    (OriginalFamily.value_exact (P.completedTable G Gamma hmem h) KSourceTransport.nativeEdges r).symm

/-- The NEW returned-LP programme owns its original retained-row query,
nullary context multiplication and infeasible-zero handling. No separate old
EO evaluator or duplicate completion preprocessing is run here. -/
def completedComputes : Computes
    (RawClosedNetwork.validatedEncoding s 1 (P.completedArity G Gamma hmem h))
    (Fields.completedPresentation G Gamma hmem h).encoding (Fields.completedValue G Gamma hmem h) :=
  congrComputes
    ((EOF.computes (P.completedTable G Gamma hmem h) (eoCondition G Gamma hmem h)).andThen
      (returnedToCompleted G Gamma hmem h)) (returned_recovery G Gamma hmem h)

def nativeOutput (r : Input (s:=s) (arity:=arity)) :
    familyField (KSourceTransport.nativeCoefficient G) :=
  ((SingleWeightCompletion.OptionalQuery.query (P.native G) (P.layer G Gamma hmem h) r).map
    (fun q => Fields.completedInclusion G Gamma hmem h (Fields.completedValue G Gamma hmem h q))).getD 0

def evaluator : Computes
    (RawClosedNetwork.validatedEncoding s 1 (P.completedArity G Gamma hmem h))
    (KSourceTransport.nativePresentation G).encoding
    (fun q => Fields.completedInclusion G Gamma hmem h (Fields.completedValue G Gamma hmem h q)) :=
  (completedComputes G Gamma hmem h).andThen (Fields.completedInclusionComputes G Gamma hmem h)

/-- The old OptionalQuery controls the actual completion provider. This
second physical OptionMap controls the WHOLE returned-LP evaluator. -/
def outputComputes : Computes (inputEncoding (s:=s) (arity:=arity))
    (KSourceTransport.nativePresentation G).encoding (nativeOutput G Gamma hmem h) :=
  ((SingleWeightCompletion.OptionalQuery.computes (P.native G) (P.layer G Gamma hmem h)).andThen
    (OptionMap.computes (evaluator G Gamma hmem h))).andThen
      (OptionalValue.getDComputes (KSourceTransport.nativePresentation G).encoding 0)

private theorem inclusion_eq_of_ambient {E F : IntermediateField ℚ AlgebraicComplex}
    (hEF : E ≤ F) (x : E) (y : F) (hxy : (x : AlgebraicComplex)=(y : AlgebraicComplex)) :
    IntermediateField.inclusion hEF x=y :=
  Subtype.ext ((IntermediateField.coe_inclusion hEF x).trans hxy)

private theorem zero_eq_of_ambient {E : IntermediateField ℚ AlgebraicComplex}
    (y : E) (hy : (y : AlgebraicComplex)=0) : (0 : E)=y :=
  Subtype.ext hy.symm

theorem native_correct (r : Input (s:=s) (arity:=arity)) :
    nativeOutput G Gamma hmem h r=KSourceTransport.nativeValue G r := by
  classical
  by_cases ha : SingleWeightCompletion.OptionalQuery.Accept (P.native G) (P.layer G Gamma hmem h) r
  · have hv : nativeOutput G Gamma hmem h r=Fields.completedInclusion G Gamma hmem h
        (Fields.completedValue G Gamma hmem h
          (SingleWeightCompletion.OptionalQuery.goodQuery (P.native G) (P.layer G Gamma hmem h) ⟨r,ha⟩)) := by
      simp [nativeOutput,SingleWeightCompletion.OptionalQuery.query,
        SingleWeightCompletion.OptionalQuery.select,ha]
    rw [hv]
    apply inclusion_eq_of_ambient
      (Holant.LocalDrafts.Tractability.EOEvaluation.SingleWeightSource.Fields.completed_le_native G Gamma hmem h)
    exact (OriginalFamily.value_exact (P.completedTable G Gamma hmem h) KSourceTransport.nativeEdges
      (SingleWeightCompletion.OptionalQuery.goodQuery (P.native G) (P.layer G Gamma hmem h) ⟨r,ha⟩)).trans
        ((SingleWeightCompletion.OptionalQuery.accepted_value (P.native G) (P.layer G Gamma hmem h) ⟨r,ha⟩).trans
          (OriginalFamily.value_exact (P.native G) KSourceTransport.nativeEdges r).symm)
  · have hv : nativeOutput G Gamma hmem h r=0 := by
      simp [nativeOutput,SingleWeightCompletion.OptionalQuery.query,
        SingleWeightCompletion.OptionalQuery.select,ha]
    rw [hv]
    exact zero_eq_of_ambient (KSourceTransport.nativeValue G r)
      ((OriginalFamily.value_exact (P.native G) KSourceTransport.nativeEdges r).trans
        (SingleWeightCompletion.OptionalQuery.reject_zero (P.native G) (P.layer G Gamma hmem h)
          (P.layer_spec G Gamma hmem h) r ha))

def nativeComputes : Computes (inputEncoding (s:=s) (arity:=arity))
    (KSourceTransport.nativePresentation G).encoding (KSourceTransport.nativeValue G) :=
  congrComputes (outputComputes G Gamma hmem h) (native_correct G Gamma hmem h)

/-- UNIQUE original ordinary equality-graph endpoint. No EO Family,
completed graph, answer, LP solver or layer witness is a source parameter. -/
def computes : Computes (inputEncoding (s:=s) (arity:=arity))
    (presentation G).encoding (value G) :=
  congrComputes ((nativeComputes G Gamma hmem h).andThen (KSourceTransport.recoverOriginal G))
    (fun r => FamilyAnswerTransport.recover_exact
      (KSourceTransport.originalCoefficient G) (KSourceTransport.nativeCoefficient G)
      (value G r) (KSourceTransport.nativeValue G r) (KSourceTransport.value_exact G r))

include hmem h in
theorem inFP : InFP (inputEncoding (s:=s) (arity:=arity))
    (presentation G).encoding (value G) := (computes G Gamma hmem h).inFP

/-- Two actual OptionMap transitions and no evaluator transition. -/
theorem rejected_evaluator_run : Raw.RunsOn (OptionMap.machine (evaluator G Gamma hmem h).machine).computer.step
    (initList (OptionMap.machine (evaluator G Gamma hmem h).machine).computer [false])
    (haltList (OptionMap.machine (evaluator G Gamma hmem h).machine).computer [false]) 2 :=
  OptionMap.none_exact (evaluator G Gamma hmem h).machine

/-- The observed positive tag contains precisely the old same-component,
ordered-pin completed graph, rather than a graph supplied to this factory. -/
theorem accepted_query (r : Input (s:=s) (arity:=arity))
    (ha : SingleWeightCompletion.OptionalQuery.Accept (P.native G) (P.layer G Gamma hmem h) r) :
    SingleWeightCompletion.OptionalQuery.query (P.native G) (P.layer G Gamma hmem h) r=
      some (SingleWeightCompletion.OptionalQuery.goodQuery (P.native G) (P.layer G Gamma hmem h) ⟨r,ha⟩) := by
  classical
  simp [SingleWeightCompletion.OptionalQuery.query,SingleWeightCompletion.OptionalQuery.select,ha]

theorem rejected_query (r : Input (s:=s) (arity:=arity))
    (hr : ¬SingleWeightCompletion.OptionalQuery.Accept (P.native G) (P.layer G Gamma hmem h) r) :
    SingleWeightCompletion.OptionalQuery.query (P.native G) (P.layer G Gamma hmem h) r=none := by
  classical
  simp [SingleWeightCompletion.OptionalQuery.query,SingleWeightCompletion.OptionalQuery.select,hr]

private theorem absent_execution {A B : Type} {ea : Encoding A Bool} {eb : Encoding B Bool}
    {f : A → Option B} (M : Computes ea (optionEncoding eb) f) (x : A) (hx : f x=none) :
    Raw.RunsOn M.machine.computer.step (initList M.machine.computer (ea.encode x))
      (haltList M.machine.computer [false]) (M.outputs x).steps := by
  have hr : Raw.RunsOn M.machine.computer.step (initList M.machine.computer (ea.encode x))
      (haltList M.machine.computer ((optionEncoding eb).encode (f x))) (M.outputs x).steps :=
    (M.outputs x).evals_in_steps
  have hw : (optionEncoding eb).encode (f x)=[false] :=
    congrArg (optionEncoding eb).encode hx
  exact (congrArg (fun word : List Bool =>
    Raw.RunsOn M.machine.computer.step (initList M.machine.computer (ea.encode x))
      (haltList M.machine.computer word) (M.outputs x).steps) hw).mp hr

/-- The actual old accept/charge scanner emits the absent byteword which
the two-transition evaluator controller above consumes. -/
theorem rejected_query_execution (r : Input (s:=s) (arity:=arity))
    (hr : ¬SingleWeightCompletion.OptionalQuery.Accept (P.native G) (P.layer G Gamma hmem h) r) :
    Raw.RunsOn (SingleWeightCompletion.OptionalQuery.computes (P.native G) (P.layer G Gamma hmem h)).machine.computer.step
      (initList (SingleWeightCompletion.OptionalQuery.computes (P.native G) (P.layer G Gamma hmem h)).machine.computer
        (inputEncoding.encode r))
      (haltList (SingleWeightCompletion.OptionalQuery.computes (P.native G) (P.layer G Gamma hmem h)).machine.computer [false])
      ((SingleWeightCompletion.OptionalQuery.computes (P.native G) (P.layer G Gamma hmem h)).outputs r).steps :=
  absent_execution (SingleWeightCompletion.OptionalQuery.computes (P.native G) (P.layer G Gamma hmem h)) r
    (rejected_query G Gamma hmem h r hr)

theorem rejected_zero (r : Input (s:=s) (arity:=arity))
    (hr : ¬SingleWeightCompletion.OptionalQuery.Accept (P.native G) (P.layer G Gamma hmem h) r) :
    value G r=0 := by
  apply Subtype.ext
  change (value G r : AlgebraicComplex)=0
  calc
    _ = (KSourceTransport.nativeValue G r : AlgebraicComplex) := (KSourceTransport.value_exact G r).symm
    _ = (r.val.realize r.property (P.native G) KSourceTransport.nativeEdges).denote Fin.elim0 :=
      OriginalFamily.value_exact (P.native G) KSourceTransport.nativeEdges r
    _ = 0 := SingleWeightCompletion.OptionalQuery.reject_zero (P.native G) (P.layer G Gamma hmem h)
      (P.layer_spec G Gamma hmem h) r hr

theorem answer_ambient (r : Input (s:=s) (arity:=arity)) :
    (value G r : AlgebraicComplex)=(r.val.realize r.property G KSourceTransport.equalityEdges).denote Fin.elim0 :=
  OriginalFamily.value_exact G KSourceTransport.equalityEdges r

def timePolynomial : Polynomial ℕ := (computes G Gamma hmem h).time
def primitivePolynomial : Polynomial ℕ := FixedFieldMachines.primitivePolynomial (computes G Gamma hmem h)
def storagePolynomial : Polynomial ℕ := Polynomial.X+primitivePolynomial G Gamma hmem h

theorem clock : timePolynomial G Gamma hmem h=(computes G Gamma hmem h).time := rfl
theorem programme : (computes G Gamma hmem h).machine=
    (nativeComputes G Gamma hmem h).machine.compose (KSourceTransport.recoverOriginal G).machine := rfl
theorem optional_programme : (outputComputes G Gamma hmem h).machine=
    ((SingleWeightCompletion.OptionalQuery.computes (P.native G) (P.layer G Gamma hmem h)).machine.compose
      (OptionMap.machine (evaluator G Gamma hmem h).machine)).compose
        (OptionalValue.getDComputes (KSourceTransport.nativePresentation G).encoding 0).machine := rfl

theorem execution (r : Input (s:=s) (arity:=arity)) :
    Raw.RunsOn (computes G Gamma hmem h).machine.computer.step
      (initList (computes G Gamma hmem h).machine.computer (inputEncoding.encode r))
      (haltList (computes G Gamma hmem h).machine.computer ((presentation G).encoding.encode (value G r)))
      ((computes G Gamma hmem h).outputs r).steps := ((computes G Gamma hmem h).outputs r).evals_in_steps
theorem steps_bound (r : Input (s:=s) (arity:=arity)) :
    ((computes G Gamma hmem h).outputs r).steps≤
      (timePolynomial G Gamma hmem h).eval (inputEncoding.encode r).length :=
  ((computes G Gamma hmem h).outputs r).steps_le_m
theorem primitive_bound (r : Input (s:=s) (arity:=arity)) :
    primitiveCost (computes G Gamma hmem h).machine ((computes G Gamma hmem h).outputs r).steps
      (some (initList (computes G Gamma hmem h).machine.computer (inputEncoding.encode r)))≤
      (primitivePolynomial G Gamma hmem h).eval (inputEncoding.encode r).length :=
  computes_primitive_cost (computes G Gamma hmem h) r
theorem output_bits (r : Input (s:=s) (arity:=arity)) :
    ((presentation G).encoding.encode (value G r)).length≤
      (computes G Gamma hmem h).outputBound.bound.eval (inputEncoding.encode r).length :=
  (computes G Gamma hmem h).outputBound.length_le r

/-- Every actual prefix inside the installed clock pays its primitive
growth; outputBound is used only for the final answer word. -/
theorem temporary_bits (r : Input (s:=s) (arity:=arity)) (i : ℕ)
    (hi : i≤(timePolynomial G Gamma hmem h).eval (inputEncoding.encode r).length)
    (cfg : (computes G Gamma hmem h).machine.Config)
    (hc : Raw.RunsOn (computes G Gamma hmem h).machine.computer.step
      (initList (computes G Gamma hmem h).machine.computer (inputEncoding.encode r)) cfg i) :
    stackSize cfg.stk≤(storagePolynomial G Gamma hmem h).eval (inputEncoding.encode r).length := by
  have hs := (computes G Gamma hmem h).machine.run_size_le _ cfg i hc
  rw [Machine.size_init] at hs
  have hb := Nat.mul_le_mul_right (computes G Gamma hmem h).machine.primitiveBudget hi
  apply hs.trans
  simpa only [storagePolynomial,primitivePolynomial,FixedFieldMachines.primitivePolynomial,timePolynomial,
    Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C] using
      Nat.add_le_add_left hb (inputEncoding.encode r).length

end
end Holant.LocalDrafts.MainChain.ReturnedLPSingleWeightSource
