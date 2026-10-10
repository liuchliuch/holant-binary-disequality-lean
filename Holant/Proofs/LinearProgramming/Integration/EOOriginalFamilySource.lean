import Holant.Proofs.LinearProgramming.Integration.EOCommonPointPairingConsumer
import Holant.Proofs.Reductions.RootPreprocessing.FieldTransport
import Holant.Proofs.Reductions.RootPreprocessing.BoundaryLaws
import Holant.Proofs.Algorithms.FamilyAnswerTransport
import Holant.Complexity.FixedFieldMachines.Concrete


namespace Holant.LocalDrafts.RemoteWork.RationalLP.Integration.EOOriginalFamilySource
open Turing Computability Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.Hardness
open GeneralExtraction
open Holant.LocalDrafts.Tractability.EOEvaluation
set_option backward.isDefEq.respectTransparency false
noncomputable section
variable {s : ℕ} {arity : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (arity i.val))

abbrev Input := RootPreprocessing.Input (s:=s) (a:=arity)
abbrev inputEncoding := RootPreprocessing.sourceEncoding (s:=s) (a:=arity)
abbrev presentation := RootPreprocessing.sourcePresentation G
abbrev value := RootPreprocessing.sourceValue G
abbrev count := RootPreprocessing.count G
abbrev targetArity := RootPreprocessing.targetArity G
abbrev targetTable := RootPreprocessing.targetTable G

/-- The entire dependent signature equality retains the original port order;
it is the existing root lookup at the same retained occurrence index. -/
theorem target_signature (j : Fin (count G)) :
    (⟨targetArity G j.val,targetTable G j⟩ : AnySignature AlgebraicComplex) =
      ⟨arity (RootPreprocessing.includeLabel G j).val,
        G (RootPreprocessing.includeLabel G j)⟩ := by
  exact (Sigma.eta (FactorSaturation.OriginalCodec.rootLookup
    (RootPreprocessing.signature G) j.val)).trans
      (FactorSaturation.OriginalCodec.rootLookup_old (RootPreprocessing.signature G) j)

theorem target_preprocessed : Preprocessed
    (Holant.LocalDrafts.Tractability.EOEvaluation.Source.signatureSet (targetTable G)) := by
  rintro f ⟨j,rfl⟩
  exact (congrArg (fun f : AnySignature AlgebraicComplex => 0 < f.1 ∧ f.2 ≠ 0)
    (target_signature G j)).mpr (RootPreprocessing.included_kept G j)

theorem target_subset :
    Holant.LocalDrafts.Tractability.EOEvaluation.Source.signatureSet (targetTable G) ⊆
      preprocess (Holant.LocalDrafts.Tractability.EOEvaluation.Source.signatureSet G) := by
  rintro f ⟨j,rfl⟩
  have hm : (⟨arity (RootPreprocessing.includeLabel G j).val,
      G (RootPreprocessing.includeLabel G j)⟩ : AnySignature AlgebraicComplex) ∈
        preprocess (Holant.LocalDrafts.Tractability.EOEvaluation.Source.signatureSet G) :=
    ⟨⟨RootPreprocessing.includeLabel G j,rfl⟩,RootPreprocessing.included_kept G j⟩
  exact (congrArg (fun f : AnySignature AlgebraicComplex =>
    f ∈ preprocess (Holant.LocalDrafts.Tractability.EOEvaluation.Source.signatureSet G))
      (target_signature G j)).mpr hm

variable (h : EOTract
  (preprocess (Holant.LocalDrafts.Tractability.EOEvaluation.Source.signatureSet G)))

/-- Same retained array; subset inheritance retains the ORIGINAL shared sign
and A/P class. No EO Family or new class witness is accepted from the caller. -/
def eoFamily : Holant.LocalDrafts.Tractability.EOEvaluation.Source.Family
    (count G) (targetArity G) where
  signatures := targetTable G
  preprocessed := target_preprocessed G
  tract := h.mono_family (target_subset G)

abbrev targetCoefficient := OriginalFamily.coefficient (targetTable G) RootPreprocessing.nativeX
abbrev targetPresentation := OriginalFamily.presentation (targetTable G) RootPreprocessing.nativeX
abbrev targetValue := OriginalFamily.value (targetTable G) RootPreprocessing.nativeX
abbrev retainedCoefficient := GeneralOriginalTarget.coefficients (targetTable G)

private abbrev backendCoefficient :=
  CandidateExecution.Backend.sourceCoefficient (eoFamily G h)

/-- The new backend returns its actual original-Q presentation. This physical
matrix programme produces the prescribed target presentation; no equality of
coordinate words or implicit field cast supplies an answer conversion. -/
private def backendToTarget : Computes
    (CandidateExecution.Backend.sourcePresentation (eoFamily G h)).encoding
    (targetPresentation G).encoding
    (FamilyAnswerTransport.recover (targetCoefficient G) (backendCoefficient G h)) :=
  FamilyAnswerTransport.computes (targetCoefficient G) (backendCoefficient G h)
    (OriginalFamily.coefficient_algebraic (targetTable G) RootPreprocessing.nativeX)
    (CandidateExecution.Backend.sourceAlgebraic (eoFamily G h))

/-- Both ambient values are the same retained raw graph, same signature table
and literal native-X edge. Ambient network equality justifies the matrix
retraction; it does not assert equality of the chosen coordinate encodings. -/
private theorem backend_recovery (r : RootPreprocessing.TargetInput G) :
    FamilyAnswerTransport.recover (targetCoefficient G) (backendCoefficient G h)
      (CandidateExecution.Backend.sourceValue (eoFamily G h) r) = targetValue G r := by
  apply FamilyAnswerTransport.recover_exact (targetCoefficient G) (backendCoefficient G h)
    (targetValue G r) (CandidateExecution.Backend.sourceValue (eoFamily G h) r)
  change (OriginalFamily.value (targetTable G) CandidateExecution.Catalogue.kernels r :
      AlgebraicComplex) =
    (OriginalFamily.value (targetTable G) RootPreprocessing.nativeX r : AlgebraicComplex)
  exact (OriginalFamily.value_exact (targetTable G) CandidateExecution.Catalogue.kernels r).trans
    (OriginalFamily.value_exact (targetTable G) RootPreprocessing.nativeX r).symm

/-- One actual common-point run supplies the returned mask, which drives the
old Graph and Backend machines. Both failure tags remain in that producer
until physical getD instructions emit field zero. The resulting answer then
passes through the real target-presentation matrix programme above. -/
def eoComputes : Computes
    (RawClosedNetwork.validatedEncoding (count G) 1 (targetArity G))
    (targetPresentation G).encoding (targetValue G) :=
  congrComputes
    ((EOCommonPointPairingConsumer.Source.computes (eoFamily G h)).andThen
      (backendToTarget G h))
    (backend_recovery G h)

/-- Actual matrix conversion, not equality of separately chosen field codecs.
The target graph/value is unchanged; only the answer representation changes. -/
def eoToRetained : Computes (targetPresentation G).encoding
    (RootPreprocessing.retainedPresentation G).encoding
    (FamilyAnswerTransport.recover (retainedCoefficient G) (targetCoefficient G)) :=
  FamilyAnswerTransport.computes (retainedCoefficient G) (targetCoefficient G)
    (GeneralOriginalTarget.coefficients_algebraic (targetTable G))
    (OriginalFamily.coefficient_algebraic (targetTable G) RootPreprocessing.nativeX)

theorem retained_recovery (r : RootPreprocessing.TargetInput G) :
    FamilyAnswerTransport.recover (retainedCoefficient G) (targetCoefficient G)
      (targetValue G r) = RootPreprocessing.retainedValue G r := by
  apply FamilyAnswerTransport.recover_exact (retainedCoefficient G) (targetCoefficient G)
    (RootPreprocessing.retainedValue G r) (targetValue G r)
  change (targetValue G r : AlgebraicComplex) =
    (RootPreprocessing.retainedValue G r : AlgebraicComplex)
  rw [OriginalFamily.value_exact,RootPreprocessing.retained_exact_value]
  rfl

def retainedComputes : Computes
    (RawClosedNetwork.validatedEncoding (count G) 1 (targetArity G))
    (RootPreprocessing.retainedPresentation G).encoding (RootPreprocessing.retainedValue G) :=
  congrComputes ((eoComputes G h).andThen (eoToRetained G)) (retained_recovery G)

/-- The original bytes produce the existing optional/filter query. Even a zero
input uses that provider's certified empty target, then runs the real backend. -/
def queriedComputes : Computes (inputEncoding (s:=s) (arity:=arity))
    (presentation G).encoding
    (fun r => RootPreprocessing.embedding G
      (RootPreprocessing.retainedValue G (RootPreprocessing.query G r))) :=
  ((RootPreprocessing.queryComputes G).andThen (retainedComputes G h)).andThen
    (RootPreprocessing.embeddingComputes G)

/-- Unique original-family endpoint. Both providers read the original input;
fixed-field multiplication restores every actual nullary scalar occurrence. -/
def computes : Computes (inputEncoding (s:=s) (arity:=arity))
    (presentation G).encoding (value G) :=
  congrComputes
    ((pairComputes (RootPreprocessing.contextComputes G) (queriedComputes G h)).andThen
      (Concrete.fieldMultiplication (presentation G)))
    (fun r => (RootPreprocessing.field_recovery G r).symm)

include h in
theorem inFP : InFP (inputEncoding (s:=s) (arity:=arity))
    (presentation G).encoding (value G) := (computes G h).inFP

/-- Original labels, native-X edge and original graph, rather than the reduced
family's value passed off as the source answer. -/
theorem answer_ambient (r : Input (s:=s) (arity:=arity)) :
    (value G r : AlgebraicComplex) =
      (r.val.realize r.property G RootPreprocessing.nativeX).denote Fin.elim0 :=
  RootPreprocessing.source_exact G r

theorem zero_answer (r : Input (s:=s) (arity:=arity))
    (hz : ¬ RootPreprocessing.Clean G r.val) : value G r = 0 := by
  apply Subtype.ext
  change (value G r : AlgebraicComplex) = 0
  rw [answer_ambient]
  exact RootPreprocessing.zero_value G r hz

theorem empty_answer : value G (RootPreprocessing.emptyInput (s:=s) (a:=arity)) = 1 :=
  RootPreprocessing.empty_value G

theorem nullary_answer (r : Input (s:=s) (arity:=arity))
    (hn : ∀ row ∈ r.val.vertices, arity row.1 = 0) :
    value G r = RootPreprocessing.context G r := RootPreprocessing.nullary_value G r hn

theorem execution (r : Input (s:=s) (arity:=arity)) :
    RawSource.RunsOn (computes G h).machine.computer.step
      (initList (computes G h).machine.computer (inputEncoding.encode r))
      (haltList (computes G h).machine.computer ((presentation G).encoding.encode (value G r)))
      ((computes G h).outputs r).steps := ((computes G h).outputs r).evals_in_steps

theorem execution_zero (r : Input (s:=s) (arity:=arity))
    (hz : ¬ RootPreprocessing.Clean G r.val) :
    RawSource.RunsOn (computes G h).machine.computer.step
      (initList (computes G h).machine.computer (inputEncoding.encode r))
      (haltList (computes G h).machine.computer ((presentation G).encoding.encode 0))
      ((computes G h).outputs r).steps := by
  simpa only [zero_answer G r hz] using execution G h r

theorem steps_bound (r : Input (s:=s) (arity:=arity)) :
    ((computes G h).outputs r).steps ≤
      (computes G h).time.eval (inputEncoding.encode r).length :=
  ((computes G h).outputs r).steps_le_m

theorem primitive_bound (r : Input (s:=s) (arity:=arity)) :
    primitiveCost (computes G h).machine ((computes G h).outputs r).steps
      (some (initList (computes G h).machine.computer (inputEncoding.encode r))) ≤
      (primitivePolynomial (computes G h)).eval (inputEncoding.encode r).length :=
  computes_primitive_cost (computes G h) r

theorem output_bits (r : Input (s:=s) (arity:=arity)) :
    ((presentation G).encoding.encode (value G r)).length ≤
      (computes G h).outputBound.bound.eval (inputEncoding.encode r).length :=
  (computes G h).outputBound.length_le r

theorem temporary_bits (r : Input (s:=s) (arity:=arity)) (i : ℕ)
    (hi : i ≤ ((computes G h).outputs r).steps)
    (c : (computes G h).machine.Config)
    (hc : (fun p => p.bind (computes G h).machine.computer.step)^[i]
      (some (initList (computes G h).machine.computer (inputEncoding.encode r))) = some c) :
    stackSize c.stk ≤
      (Polynomial.X + primitivePolynomial (computes G h)).eval (inputEncoding.encode r).length := by
  have hs := (computes G h).machine.run_size_le _ c i hc
  rw [Machine.size_init] at hs
  have hb := Nat.mul_le_mul_right (computes G h).machine.primitiveBudget
    (hi.trans ((computes G h).outputs r).steps_le_m)
  apply hs.trans
  simpa only [FixedFieldMachines.primitivePolynomial, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_mul, Polynomial.eval_C] using
    Nat.add_le_add_left hb (inputEncoding.encode r).length

end
end Holant.LocalDrafts.RemoteWork.RationalLP.Integration.EOOriginalFamilySource
