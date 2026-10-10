import Holant.Proofs.BinaryInterpolation.SingularExtraction.Composition.SourceCodec
import Holant.Proofs.BinaryInterpolation.SourceTransport
import Holant.Proofs.Algorithms.BinaryOriginalTarget


noncomputable section
namespace Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.Composition.CanonicalOracle
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity Computability
open BinaryCompose FixedFieldMachines FixedGadgetSubstitution.Compiler
open Holant.LocalDrafts.MainChain
open Holant.Complexity.UniversalPairReduction.ThreeQuery
set_option backward.isDefEq.respectTransparency false
variable {s : ℕ} {arity : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (arity i.val))

abbrev family := SourceTransport.family G
abbrev algebraic := SourceTransport.family_algebraic G
abbrev field := BinaryOriginalTarget.originalField (family G)
abbrev presentation := BinaryOriginalTarget.originalPresentation (family G) (algebraic G)
abbrev value := BinaryOriginalTarget.originalValue (family G) (algebraic G)
abbrev encoding := (presentation G).encoding

theorem field_image : (OriginalField.field G).map (algebraicClosure ℚ ℂ).val = field G := by
  change (IntermediateField.adjoin ℚ (Set.range (OriginalField.coefficient G))).map
    (algebraicClosure ℚ ℂ).val =
      IntermediateField.adjoin ℚ (Set.range (BinaryOriginalTarget.coefficients (family G)))
  rw [IntermediateField.adjoin_map, ← Set.range_comp]
  rfl

def fieldEquiv : OriginalField.field G ≃ₐ[ℚ] field G :=
  (IntermediateField.equivMap (OriginalField.field G) (algebraicClosure ℚ ℂ).val).trans
    (IntermediateField.equivOfEq (field_image G))

theorem fieldEquiv_coe (x : OriginalField.field G) :
    (fieldEquiv G x : ℂ) = SourceTransport.inclusion (x : AlgebraicComplex) := by
  rfl

theorem value_equiv (q : ExactSignatureTables.Input s 1 arity) :
    value G q = fieldEquiv G (OriginalField.value G q) := by
  apply Subtype.ext
  rw [BinaryOriginalTarget.target_value_exact,fieldEquiv_coe,OriginalField.value_exact]
  exact (SourceTransport.closed_value G q).symm

def decodeComputes : Computes (encoding G) (OriginalField.encoding G) (fieldEquiv G).symm :=
  FieldCodec.computes (presentation G) (OriginalField.presentation G) (fieldEquiv G).symm.toLinearMap

theorem decode_primitive (x : field G) :
    primitiveCost (decodeComputes G).machine ((decodeComputes G).outputs x).steps
      (some (Turing.initList (decodeComputes G).machine.computer ((encoding G).encode x))) ≤
      (primitivePolynomial (decodeComputes G)).eval ((encoding G).encode x).length :=
  computes_primitive_cost (decodeComputes G) x

theorem decoded_value (q : ExactSignatureTables.Input s 1 arity) :
    (fieldEquiv G).symm (value G q) = OriginalField.value G q := by
  rw [value_equiv,AlgEquiv.symm_apply_apply]

def transport : LengthControlledOracleReduction
    (FieldReduction.queryEncoding (s:=s) (arity:=arity)) (OriginalField.encoding G)
    (FieldReduction.queryEncoding (s:=s) (arity:=arity)) (encoding G)
    (OriginalField.value G) (value G) :=
  controlledOneQueryOfEq (identityComputes (FieldReduction.queryEncoding (s:=s) (arity:=arity)))
    (decodeComputes G)
    ((BinaryOriginalTarget.originalTables (family G) (algebraic G)).outputBound (presentation G))
    (OriginalField.value G) (fun q => (decoded_value G q).symm)

variable (u v : Bool → AlgebraicComplex) (U : PowerMacro G u) (V : PowerMacro G v)

/-- Central inlining also reaches the literal canonical target codec; the
source answer is already free of macro-scale coordinates at this boundary. -/
def inlinedReduction : PolyTimeOracleReduction
    (FieldReduction.inputEncoding (s:=s) (arity:=arity)) (SourceCodec.encoding G u v)
    (FieldReduction.queryEncoding (s:=s) (arity:=arity)) (encoding G)
    (SourceCodec.value G u v) (value G) :=
  (SourceCodec.controlled G u v U V).compose (transport G).reduction

theorem inlined_time : (inlinedReduction G u v U V).time =
    (SourceCodec.controlled G u v U V).compositionTimePolynomial (transport G).reduction := rfl

def post (z : List (field G) × FieldReduction.Context (CommonField.field G u v U V)) : SourceCodec.field G u v :=
  SourceCodec.post G u v U V ([(fieldEquiv G).symm (z.1.getD 0 0)],z.2)

def postComputes : Computes
    (OracleBatch.contextEncoding (encoding G) (FieldReduction.contextEncoding (CommonField.presentation G u v U V)))
    (SourceCodec.encoding G u v) (post G u v U V) := by
  let head := ((Wiring.firstComputes (framedListEncoding (encoding G))
    (FieldReduction.contextEncoding (CommonField.presentation G u v U V))).andThen
      (getDComputes (encoding G) 0 0)).andThen (decodeComputes G)
  let one := fixedListComputes _ (OriginalField.encoding G)
    (fun (z : List (field G) × FieldReduction.Context (CommonField.field G u v U V)) (_ : Unit) => (fieldEquiv G).symm (z.1.getD 0 0)) (fun _ => head) [()]
  exact (pairComputes one (Wiring.secondComputes (framedListEncoding (encoding G))
    (FieldReduction.contextEncoding (CommonField.presentation G u v U V)))).andThen
      (SourceCodec.postComputes G u v U V)

theorem recovery (r : OriginalQuery.UnaryInput (s:=s) (arity:=arity)) :
    SourceCodec.value G u v r = post G u v U V
      (OracleBatch.answers (value G) (OriginalTarget.pre G u v U V r)) := by
  change _ = SourceCodec.post G u v U V
    ([(fieldEquiv G).symm (value G (OriginalTarget.query G u v U V r))],
      (OriginalTarget.pre G u v U V r).2)
  rw [decoded_value]
  exact SourceCodec.recovery G u v U V r

def reduction : PolyTimeOracleReduction
    (FieldReduction.inputEncoding (s:=s) (arity:=arity)) (SourceCodec.encoding G u v)
    (FieldReduction.queryEncoding (s:=s) (arity:=arity)) (encoding G)
    (SourceCodec.value G u v) (value G) :=
  OracleBatch.of_eq (OriginalTarget.preComputes G u v U V) (postComputes G u v U V)
    ((BinaryOriginalTarget.originalTables (family G) (algebraic G)).outputBound (presentation G))
    (SourceCodec.value G u v) (recovery G u v U V)

theorem run_trace (oracle : List Bool → List Bool)
    (ho : RepresentsOracle (FieldReduction.queryEncoding (s:=s) (arity:=arity)) (encoding G)
      (value G) oracle) (r : OriginalQuery.UnaryInput (s:=s) (arity:=arity)) :
    ∃ t ≤ (reduction G u v U V).time.eval ((FieldReduction.inputEncoding (s:=s) (arity:=arity)).encode r).length,
      OracleBatch.RunsTrace (reduction G u v U V).machine oracle
        ((reduction G u v U V).machine.init ((FieldReduction.inputEncoding (s:=s) (arity:=arity)).encode r))
        ((reduction G u v U V).machine.output ((SourceCodec.encoding G u v).encode (SourceCodec.value G u v r))) t
        [(FieldReduction.queryEncoding (s:=s) (arity:=arity)).encode (OriginalTarget.query G u v U V r)] := by
  have h := OracleBatch.of_eq_run_trace (OriginalTarget.preComputes G u v U V) (postComputes G u v U V)
      ((BinaryOriginalTarget.originalTables (family G) (algebraic G)).outputBound (presentation G))
      (SourceCodec.value G u v) (recovery G u v U V) oracle ho r
  simp only [OriginalTarget.pre,FieldReduction.pre,List.map_cons,List.map_nil] at h
  exact h

def controlled : LengthControlledOracleReduction
    (FieldReduction.inputEncoding (s:=s) (arity:=arity)) (SourceCodec.encoding G u v)
    (FieldReduction.queryEncoding (s:=s) (arity:=arity)) (encoding G)
    (SourceCodec.value G u v) (value G) where
  reduction := reduction G u v U V
  targetOutput := (BinaryOriginalTarget.originalTables (family G) (algebraic G)).outputBound (presentation G)
  queryBound := OriginalTarget.queryPolynomial G u v U V
  safeQuery oracle ho r t c hr hq := by
    obtain ⟨N,_,ht⟩ := run_trace G u v U V oracle ho r
    have hm := TraceQueryControl.transcript_member ht t c hr hq
    have he : c.stk (reduction G u v U V).machine.queryStack =
        (FieldReduction.queryEncoding (s:=s) (arity:=arity)).encode (OriginalTarget.query G u v U V r) := by
      simpa only [List.mem_singleton] using hm
    refine ⟨OriginalTarget.query G u v U V r,he,?_⟩
    rw [he]
    exact FieldReduction.query_length (OriginalTarget.original G u v U V)
      (OriginalTarget.left G u v U V) (OriginalTarget.right G u v U V)
      (OriginalTarget.leftMacro G u v U V) (OriginalTarget.rightMacro G u v U V) r

def primitiveBound : Polynomial ℕ :=
  Polynomial.C (reduction G u v U V).machine.primitiveBudget * (reduction G u v U V).time

theorem execution (oracle : List Bool → List Bool)
    (ho : RepresentsOracle (FieldReduction.queryEncoding (s:=s) (arity:=arity)) (encoding G)
      (value G) oracle) (r : OriginalQuery.UnaryInput (s:=s) (arity:=arity)) :
    ∃ t ≤ (reduction G u v U V).time.eval ((FieldReduction.inputEncoding (s:=s) (arity:=arity)).encode r).length,
      OracleBatch.RunsTrace (reduction G u v U V).machine oracle
        ((reduction G u v U V).machine.init ((FieldReduction.inputEncoding (s:=s) (arity:=arity)).encode r))
        ((reduction G u v U V).machine.output ((SourceCodec.encoding G u v).encode (SourceCodec.value G u v r))) t
        [(FieldReduction.queryEncoding (s:=s) (arity:=arity)).encode (OriginalTarget.query G u v U V r)] ∧
      queryCount (reduction G u v U V).machine oracle
        ((reduction G u v U V).machine.init ((FieldReduction.inputEncoding (s:=s) (arity:=arity)).encode r)) t = 1 ∧
      OracleBatch.primitiveCount (reduction G u v U V).machine oracle
        ((reduction G u v U V).machine.init ((FieldReduction.inputEncoding (s:=s) (arity:=arity)).encode r)) t ≤
        (primitiveBound G u v U V).eval ((FieldReduction.inputEncoding (s:=s) (arity:=arity)).encode r).length := by
  obtain ⟨t,ht,hr⟩ := run_trace G u v U V oracle ho r
  refine ⟨t,ht,hr,?_,?_⟩
  · simpa using hr.count
  · exact (OracleBatch.primitiveCount_le _ _ _ _).trans (by
      simpa only [primitiveBound,Polynomial.eval_mul,Polynomial.eval_C] using
        Nat.mul_le_mul_left (reduction G u v U V).machine.primitiveBudget ht)

end Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.Composition.CanonicalOracle
