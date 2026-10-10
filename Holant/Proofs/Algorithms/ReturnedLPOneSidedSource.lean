import Holant.Proofs.Tractability.EOEvaluation.OneSidedSource.Fields
import Holant.Proofs.LinearProgramming.Integration.EOOriginalFamilySource


namespace Holant.LocalDrafts.MainChain.ReturnedLPOneSidedSource
open Turing Computability Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.Hardness
noncomputable section

namespace P
export Holant.LocalDrafts.Tractability.EOEvaluation.OneSidedSource.Producer
  (Input central native native_member native_nonzero_original central_nonzero_native
   central_value_exact count targetArity targetTable)
end P
namespace Fields
export Holant.LocalDrafts.Tractability.EOEvaluation.OneSidedSource.Fields
  (centralCoefficient centralPresentation centralValue centralInclusionComputes native_recovery)
end Fields
namespace EOF
export Holant.LocalDrafts.RemoteWork.RationalLP.Integration.EOOriginalFamilySource
  (presentation value computes answer_ambient zero_answer empty_answer nullary_answer
   count targetArity targetTable)
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
variable (h : OneSidedAlternative (preprocess Gamma))

abbrev Input := P.Input (s:=s) (arity:=arity)
abbrev inputEncoding := KSourceTransport.inputEncoding (s:=s) (arity:=arity)
abbrev presentation := KSourceTransport.originalPresentation G
abbrev value := KSourceTransport.originalValue G

include hmem in
/-- Only retained nonzero positive-arity central tables need membership.
The original native member comes from the same original label and hmem. -/
theorem central_subset : preprocess (EO.signatureSet (P.central G)) ⊆
    centralFamily (kCoordinates (preprocess Gamma)) := by
  rintro f ⟨⟨i,rfl⟩,hi,hn⟩
  refine ⟨⟨arity i.val,P.native G i⟩,?_,hn,rfl⟩
  exact P.native_member G Gamma hmem i hi
    (P.native_nonzero_original G i (P.central_nonzero_native G i hn))

/-- The SAME global EO sign and A/P class are inherited, not requested as an
extra EO-family or backend input. Zero/nullary tables are removed internally. -/
def eoCondition : EOTract (preprocess (EO.signatureSet (P.central G))) :=
  h.2.mono_family (central_subset G Gamma hmem)

theorem same_retained_count : EOF.count (P.central G)=P.count G := rfl
theorem same_retained_arity : EOF.targetArity (P.central G)=P.targetArity G := rfl
theorem same_retained_table : EOF.targetTable (P.central G)=P.targetTable G := rfl

private abbrev returnedCoefficient := RootPreprocessing.sourceCoefficient (P.central G)

/-- Two prescribed coefficient presentations are connected by an ACTUAL
fixed rational matrix. Ambient equality below does not identify their bytes. -/
private def returnedToCentral : Computes (EOF.presentation (P.central G)).encoding
    (Fields.centralPresentation G).encoding
    (FamilyAnswerTransport.recover (Fields.centralCoefficient G) (returnedCoefficient G)) :=
  FamilyAnswerTransport.computes (Fields.centralCoefficient G) (returnedCoefficient G)
    (OriginalFamily.coefficient_algebraic (P.central G) KSourceTransport.nativeEdges)
    (OriginalFamily.coefficient_algebraic (P.central G) RootPreprocessing.nativeX)

private theorem returned_recovery (r : Input (s:=s) (arity:=arity)) :
    FamilyAnswerTransport.recover (Fields.centralCoefficient G) (returnedCoefficient G)
      (EOF.value (P.central G) r)=Fields.centralValue G r := by
  apply FamilyAnswerTransport.recover_exact (Fields.centralCoefficient G) (returnedCoefficient G)
    (Fields.centralValue G r) (EOF.value (P.central G) r)
  exact (EOF.answer_ambient (P.central G) r).trans
    (OriginalFamily.value_exact (P.central G) KSourceTransport.nativeEdges r).symm

/-- This is the NEW whole EO programme: its common-support mask, ordered
pairing compiler, A/P backend, infeasible-zero and zero/nullary restoration
all belong to the returned RawSource chain. No old LP machine is installed. -/
def centralComputes : Computes (inputEncoding (s:=s) (arity:=arity))
    (Fields.centralPresentation G).encoding (Fields.centralValue G) :=
  congrComputes
    ((EOF.computes (P.central G) (eoCondition G Gamma hmem h)).andThen
      (returnedToCentral G)) (returned_recovery G)

/-- The original charge-conservation theorem justifies this precise fixed
matrix conversion from central C+X to native K-inverse-G+X. -/
def nativeComputes : Computes (inputEncoding (s:=s) (arity:=arity))
    (KSourceTransport.nativePresentation G).encoding (KSourceTransport.nativeValue G) :=
  congrComputes
    ((centralComputes G Gamma hmem h).andThen (Fields.centralInclusionComputes G))
    (Fields.native_recovery G Gamma hmem h)

/-- UNIQUE original ordinary-graph entry. Ordered ports and graph bytes are
unchanged by K; its old physical answer matrix returns ORIGINAL G+equality. -/
def computes : Computes (inputEncoding (s:=s) (arity:=arity))
    (presentation G).encoding (value G) :=
  congrComputes
    ((nativeComputes G Gamma hmem h).andThen (KSourceTransport.recoverOriginal G))
    (fun r => FamilyAnswerTransport.recover_exact
      (KSourceTransport.originalCoefficient G) (KSourceTransport.nativeCoefficient G)
      (value G r) (KSourceTransport.nativeValue G r) (KSourceTransport.value_exact G r))

include hmem h in
theorem inFP : InFP (inputEncoding (s:=s) (arity:=arity))
    (presentation G).encoding (value G) := (computes G Gamma hmem h).inFP

theorem answer_ambient (r : Input (s:=s) (arity:=arity)) :
    (value G r : AlgebraicComplex)=
      (r.val.realize r.property G KSourceTransport.equalityEdges).denote Fin.elim0 :=
  OriginalFamily.value_exact G KSourceTransport.equalityEdges r

include hmem h in
private theorem central_ambient (r : Input (s:=s) (arity:=arity)) :
    (value G r : AlgebraicComplex)=(EOF.value (P.central G) r : AlgebraicComplex) := by
  calc
    _ = (KSourceTransport.nativeValue G r : AlgebraicComplex) := (KSourceTransport.value_exact G r).symm
    _ = (Fields.centralValue G r : AlgebraicComplex) := (P.central_value_exact G Gamma hmem h r).symm
    _ = _ := (OriginalFamily.value_exact (P.central G) KSourceTransport.nativeEdges r).trans
      (EOF.answer_ambient (P.central G) r).symm

include hmem h in
theorem zero_on_central_exit (r : Input (s:=s) (arity:=arity))
    (hz : ¬RootPreprocessing.Clean (P.central G) r.val) : value G r=0 := by
  apply Subtype.ext
  change (value G r : AlgebraicComplex)=0
  calc
    _ = (EOF.value (P.central G) r : AlgebraicComplex) := central_ambient G Gamma hmem h r
    _ = 0 := congrArg (fun x : RootPreprocessing.sourceField (P.central G) => (x : AlgebraicComplex))
      (EOF.zero_answer (P.central G) r hz)

include hmem h in
theorem empty_answer : value G (RootPreprocessing.emptyInput (s:=s) (a:=arity))=1 := by
  apply Subtype.ext
  change (value G (RootPreprocessing.emptyInput (s:=s) (a:=arity)) : AlgebraicComplex)=1
  calc
    _ = (EOF.value (P.central G) (RootPreprocessing.emptyInput (s:=s) (a:=arity)) : AlgebraicComplex) :=
      central_ambient G Gamma hmem h _
    _ = 1 := congrArg (fun x : RootPreprocessing.sourceField (P.central G) => (x : AlgebraicComplex))
      (EOF.empty_answer (P.central G))

include hmem h in
theorem nullary_answer (r : Input (s:=s) (arity:=arity))
    (hn : ∀row∈r.val.vertices,arity row.1=0) :
    (value G r : AlgebraicComplex)=(RootPreprocessing.context (P.central G) r : AlgebraicComplex) := by
  calc
    _ = (EOF.value (P.central G) r : AlgebraicComplex) := central_ambient G Gamma hmem h r
    _ = _ := congrArg (fun x : RootPreprocessing.sourceField (P.central G) => (x : AlgebraicComplex))
      (EOF.nullary_answer (P.central G) r hn)

def timePolynomial : Polynomial ℕ := (computes G Gamma hmem h).time
def primitivePolynomial : Polynomial ℕ := FixedFieldMachines.primitivePolynomial (computes G Gamma hmem h)
def storagePolynomial : Polynomial ℕ := Polynomial.X+primitivePolynomial G Gamma hmem h

theorem central_clock : (centralComputes G Gamma hmem h).time=
    (EOF.computes (P.central G) (eoCondition G Gamma hmem h)).time+
      2*((EOF.computes (P.central G) (eoCondition G Gamma hmem h)).outputBound.bound+1)+
      (returnedToCentral G).time.comp
        (EOF.computes (P.central G) (eoCondition G Gamma hmem h)).outputBound.bound := rfl
theorem native_clock : (nativeComputes G Gamma hmem h).time=
    (centralComputes G Gamma hmem h).time+2*((centralComputes G Gamma hmem h).outputBound.bound+1)+
      (Fields.centralInclusionComputes G).time.comp (centralComputes G Gamma hmem h).outputBound.bound := rfl
theorem ordinary_clock : (computes G Gamma hmem h).time=
    (nativeComputes G Gamma hmem h).time+2*((nativeComputes G Gamma hmem h).outputBound.bound+1)+
      (KSourceTransport.recoverOriginal G).time.comp (nativeComputes G Gamma hmem h).outputBound.bound := rfl
theorem clock : timePolynomial G Gamma hmem h=(computes G Gamma hmem h).time := rfl
theorem programme : (computes G Gamma hmem h).machine=
    (nativeComputes G Gamma hmem h).machine.compose (KSourceTransport.recoverOriginal G).machine := rfl

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

/-- Every actual prefix within the installed clock is controlled by input
bits plus genuine primitive growth. Output length is not a storage bound. -/
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
end Holant.LocalDrafts.MainChain.ReturnedLPOneSidedSource
