import Holant.Proofs.BinaryInterpolation.SingularExtraction.Composition.QueryControl
import Holant.Proofs.BinaryInterpolation.SingularExtraction.Composition.OriginalField


noncomputable section
namespace Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.Composition.OriginalTarget
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity Computability
open BinaryCompose FixedFieldMachines FixedGadgetSubstitution.Compiler
open Holant.LocalDrafts.MainChain
open Holant.Complexity.UniversalPairReduction.ThreeQuery
set_option backward.isDefEq.respectTransparency false
variable {s : ℕ} {arity : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (arity i.val))
variable (u v : Bool → AlgebraicComplex) (U : PowerMacro G u) (V : PowerMacro G v)

abbrev F := CommonField.presentation G u v U V
abbrev original := CommonField.original G u v U V
abbrev left := CommonField.left G u v U V
abbrev right := CommonField.right G u v U V
abbrev leftMacro := CommonField.leftMacro G u v U V
abbrev rightMacro := CommonField.rightMacro G u v U V
abbrev inputEncoding := FieldReduction.inputEncoding (s:=s) (arity:=arity)
abbrev queryEncoding := FieldReduction.queryEncoding (s:=s) (arity:=arity)
abbrev query := FieldReduction.query (original G u v U V) (left G u v U V) (right G u v U V)
  (leftMacro G u v U V) (rightMacro G u v U V)
abbrev pre := FieldReduction.pre (original G u v U V) (left G u v U V) (right G u v U V)
  (leftMacro G u v U V) (rightMacro G u v U V)
abbrev preComputes := FieldReduction.preComputes (F G u v U V)
  (original G u v U V) (left G u v U V) (right G u v U V)
  (leftMacro G u v U V) (rightMacro G u v U V)
abbrev caller := QueryControl.controlled (F G u v U V)
  (original G u v U V) (left G u v U V) (right G u v U V)
  (leftMacro G u v U V) (rightMacro G u v U V)
abbrev queryPolynomial := FieldReduction.queryPolynomial
  (original G u v U V) (left G u v U V) (right G u v U V)
  (leftMacro G u v U V) (rightMacro G u v U V)

/-- The central inliner sees matching common-field intermediate codecs. Its
only external oracle codec is generated from G, independently of u/v/scales. -/
def inlinedReduction : PolyTimeOracleReduction
    (inputEncoding (s:=s) (arity:=arity)) (F G u v U V).encoding
    (queryEncoding (s:=s) (arity:=arity)) (OriginalField.encoding G)
    (CommonField.sourceValue G u v U V) (OriginalField.value G) :=
  (caller G u v U V).compose (OriginalField.transport G u v U V).reduction

theorem inlined_time : (inlinedReduction G u v U V).time =
    (caller G u v U V).compositionTimePolynomial (OriginalField.transport G u v U V).reduction := rfl

theorem inlined_run_cost (oracle : List Bool → List Bool)
    (ho : RepresentsOracle (queryEncoding (s:=s) (arity:=arity)) (OriginalField.encoding G)
      (OriginalField.value G) oracle) (r : OriginalQuery.UnaryInput (s:=s) (arity:=arity)) :
    ∃ t ≤ (inlinedReduction G u v U V).time.eval ((inputEncoding (s:=s) (arity:=arity)).encode r).length,
      (inlinedReduction G u v U V).machine.run oracle
        ((inputEncoding (s:=s) (arity:=arity)).encode r) t =
        some ((inlinedReduction G u v U V).machine.output
          ((F G u v U V).encoding.encode (CommonField.sourceValue G u v U V r))) ∧
      OracleBatch.primitiveCount (inlinedReduction G u v U V).machine oracle
        ((inlinedReduction G u v U V).machine.init ((inputEncoding (s:=s) (arity:=arity)).encode r)) t ≤
        (Polynomial.C (inlinedReduction G u v U V).machine.primitiveBudget *
          (inlinedReduction G u v U V).time).eval ((inputEncoding (s:=s) (arity:=arity)).encode r).length := by
  let h := (inlinedReduction G u v U V).correct oracle ho r
  refine ⟨h.steps,h.steps_le_m,h.evals_in_steps,?_⟩
  exact (OracleBatch.primitiveCount_le _ _ _ _).trans (by
    simpa only [Polynomial.eval_mul,Polynomial.eval_C] using
      Nat.mul_le_mul_left (inlinedReduction G u v U V).machine.primitiveBudget h.steps_le_m)

def post (z : List (OriginalField.field G) × FieldReduction.Context (CommonField.field G u v U V)) :
    CommonField.field G u v U V :=
  FieldReduction.correction (original G u v U V) (left G u v U V) (right G u v U V)
    (leftMacro G u v U V) (rightMacro G u v U V)
    (OriginalField.embedding G u v U V (z.1.getD 0 0),z.2)

/-- Keep the original context and correction program. Read one exact answer,
execute its fixed rational matrix conversion, then call that correction. -/
def postComputes : Computes
    (OracleBatch.contextEncoding (OriginalField.encoding G) (FieldReduction.contextEncoding (F G u v U V)))
    (F G u v U V).encoding (post G u v U V) :=
  (pairComputes
    (((Wiring.firstComputes (framedListEncoding (OriginalField.encoding G))
      (FieldReduction.contextEncoding (F G u v U V))).andThen
        (getDComputes (OriginalField.encoding G) 0 0)).andThen
          (OriginalField.embedComputes G u v U V))
    (Wiring.secondComputes (framedListEncoding (OriginalField.encoding G))
      (FieldReduction.contextEncoding (F G u v U V)))).andThen
    (FieldReduction.correctionComputes (F G u v U V)
      (original G u v U V) (left G u v U V) (right G u v U V)
      (leftMacro G u v U V) (rightMacro G u v U V))

theorem recovery (r : OriginalQuery.UnaryInput (s:=s) (arity:=arity)) :
    CommonField.sourceValue G u v U V r =
      post G u v U V (OracleBatch.answers (OriginalField.value G) (pre G u v U V r)) := by
  have h := FieldReduction.recovery (F G u v U V)
    (original G u v U V) (left G u v U V) (right G u v U V)
    (leftMacro G u v U V) (rightMacro G u v U V) r
  change _ = FieldReduction.correction (original G u v U V) (left G u v U V) (right G u v U V)
    (leftMacro G u v U V) (rightMacro G u v U V)
    (CommonField.targetValue G u v U V (query G u v U V r),(pre G u v U V r).2) at h
  change _ = FieldReduction.correction (original G u v U V) (left G u v U V) (right G u v U V)
    (leftMacro G u v U V) (rightMacro G u v U V)
    (OriginalField.embedding G u v U V (OriginalField.value G (query G u v U V r)),
      (pre G u v U V r).2)
  rw [← OriginalField.target_eq]
  exact h

def reduction : PolyTimeOracleReduction
    (inputEncoding (s:=s) (arity:=arity)) (F G u v U V).encoding
    (queryEncoding (s:=s) (arity:=arity)) (OriginalField.encoding G)
    (CommonField.sourceValue G u v U V) (OriginalField.value G) :=
  OracleBatch.of_eq (preComputes G u v U V) (postComputes G u v U V)
    ((OriginalField.tables G).outputBound (OriginalField.presentation G))
    (CommonField.sourceValue G u v U V) (recovery G u v U V)

theorem run_trace (oracle : List Bool → List Bool)
    (ho : RepresentsOracle (queryEncoding (s:=s) (arity:=arity)) (OriginalField.encoding G)
      (OriginalField.value G) oracle) (r : OriginalQuery.UnaryInput (s:=s) (arity:=arity)) :
    ∃ t ≤ (reduction G u v U V).time.eval ((inputEncoding (s:=s) (arity:=arity)).encode r).length,
      OracleBatch.RunsTrace (reduction G u v U V).machine oracle
        ((reduction G u v U V).machine.init ((inputEncoding (s:=s) (arity:=arity)).encode r))
        ((reduction G u v U V).machine.output ((F G u v U V).encoding.encode (CommonField.sourceValue G u v U V r)))
        t [(queryEncoding (s:=s) (arity:=arity)).encode (query G u v U V r)] := by
  have h := OracleBatch.of_eq_run_trace (preComputes G u v U V) (postComputes G u v U V)
      ((OriginalField.tables G).outputBound (OriginalField.presentation G))
      (CommonField.sourceValue G u v U V) (recovery G u v U V) oracle ho r
  simp only [pre,FieldReduction.pre,List.map_cons,List.map_nil] at h
  exact h

def controlled : LengthControlledOracleReduction
    (inputEncoding (s:=s) (arity:=arity)) (F G u v U V).encoding
    (queryEncoding (s:=s) (arity:=arity)) (OriginalField.encoding G)
    (CommonField.sourceValue G u v U V) (OriginalField.value G) where
  reduction := reduction G u v U V
  targetOutput := (OriginalField.tables G).outputBound (OriginalField.presentation G)
  queryBound := queryPolynomial G u v U V
  safeQuery oracle ho r t c hr hq := by
    obtain ⟨N,_,ht⟩ := run_trace G u v U V oracle ho r
    have hm := TraceQueryControl.transcript_member ht t c hr hq
    have he : c.stk (reduction G u v U V).machine.queryStack =
        (queryEncoding (s:=s) (arity:=arity)).encode (query G u v U V r) := by
      simpa only [List.mem_singleton] using hm
    refine ⟨query G u v U V r,he,?_⟩
    rw [he]
    exact FieldReduction.query_length (original G u v U V) (left G u v U V) (right G u v U V)
      (leftMacro G u v U V) (rightMacro G u v U V) r

def primitivePolynomial : Polynomial ℕ :=
  Polynomial.C (reduction G u v U V).machine.primitiveBudget * (reduction G u v U V).time

theorem execution (oracle : List Bool → List Bool)
    (ho : RepresentsOracle (queryEncoding (s:=s) (arity:=arity)) (OriginalField.encoding G)
      (OriginalField.value G) oracle) (r : OriginalQuery.UnaryInput (s:=s) (arity:=arity)) :
    ∃ t ≤ (reduction G u v U V).time.eval ((inputEncoding (s:=s) (arity:=arity)).encode r).length,
      OracleBatch.RunsTrace (reduction G u v U V).machine oracle
        ((reduction G u v U V).machine.init ((inputEncoding (s:=s) (arity:=arity)).encode r))
        ((reduction G u v U V).machine.output ((F G u v U V).encoding.encode (CommonField.sourceValue G u v U V r)))
        t [(queryEncoding (s:=s) (arity:=arity)).encode (query G u v U V r)] ∧
      queryCount (reduction G u v U V).machine oracle
        ((reduction G u v U V).machine.init ((inputEncoding (s:=s) (arity:=arity)).encode r)) t = 1 ∧
      OracleBatch.primitiveCount (reduction G u v U V).machine oracle
        ((reduction G u v U V).machine.init ((inputEncoding (s:=s) (arity:=arity)).encode r)) t ≤
        (primitivePolynomial G u v U V).eval ((inputEncoding (s:=s) (arity:=arity)).encode r).length := by
  obtain ⟨t,ht,hr⟩ := run_trace G u v U V oracle ho r
  refine ⟨t,ht,hr,?_,?_⟩
  · simpa using hr.count
  · exact (OracleBatch.primitiveCount_le _ _ _ _).trans (by
      simpa only [primitivePolynomial,Polynomial.eval_mul,Polynomial.eval_C] using
        Nat.mul_le_mul_left (reduction G u v U V).machine.primitiveBudget ht)

/-- A direct polynomial of original graph bytes for the actual conversion's
output; the smaller original-field answer bound is included by composition. -/
def convertedAnswerBound : PolynomialOutputBound (queryEncoding (s:=s) (arity:=arity))
    (F G u v U V).encoding (fun q => OriginalField.embedding G u v U V (OriginalField.value G q)) :=
  FieldTransport.embeddedOutput (OriginalField.presentation G) (F G u v U V)
    (OriginalField.embedding G u v U V) (queryEncoding (s:=s) (arity:=arity)) (OriginalField.value G)
    ((OriginalField.tables G).outputBound (OriginalField.presentation G))

end Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.Composition.OriginalTarget
