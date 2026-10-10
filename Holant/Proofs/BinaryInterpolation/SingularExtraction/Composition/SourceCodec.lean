import Holant.Proofs.BinaryInterpolation.SingularExtraction.Composition.OriginalTarget


noncomputable section
namespace Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.Composition.SourceCodec
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose Holant.LocalDrafts.MainChain
open Holant.Complexity.UniversalPairReduction.ThreeQuery
set_option backward.isDefEq.respectTransparency false
variable {s : ℕ} {arity : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (arity i.val)) (u v : Bool → AlgebraicComplex)

abbrev signatures := Tables.typed (Tables.familyTable G u v) (s+2) (Tables.adjoinedArity s arity 1 1)
abbrev field := OriginalField.field (signatures G u v)
abbrev presentation := OriginalField.presentation (signatures G u v)
abbrev encoding := (presentation G u v).encoding
abbrev value := OriginalField.value (signatures G u v)

theorem value_exact (r : OriginalQuery.UnaryInput (s:=s) (arity:=arity)) :
    (value G u v r : AlgebraicComplex) =
      (r.val.realize r.property (signatures G u v) (fun _ => Signature.disequality)).denote Fin.elim0 :=
  OriginalField.value_exact (signatures G u v) r

variable (U : PowerMacro G u) (V : PowerMacro G v)

theorem field_le : field G u v ≤ CommonField.field G u v U V := by
  apply IntermediateField.adjoin_le_iff.mpr
  rintro z ⟨⟨i,x⟩,rfl⟩
  let y : CommonField.field G u v U V :=
    Tables.typed (Tables.familyTable (CommonField.original G u v U V)
      (CommonField.left G u v U V) (CommonField.right G u v U V))
      (s+2) (Tables.adjoinedArity s arity 1 1) i x
  have hy : (y : AlgebraicComplex) = OriginalField.coefficient (signatures G u v) ⟨i,x⟩ :=
    CommonField.familyTable_exact G u v U V i.val (List.ofFn x)
  rw [← hy]
  exact y.property

def embedding : field G u v →ₐ[ℚ] CommonField.field G u v U V :=
  IntermediateField.inclusion (field_le G u v U V)

theorem common_value (r : OriginalQuery.UnaryInput (s:=s) (arity:=arity)) :
    CommonField.sourceValue G u v U V r = embedding G u v U V (value G u v r) := by
  apply Subtype.ext
  change (CommonField.sourceValue G u v U V r : AlgebraicComplex) = (value G u v r : AlgebraicComplex)
  rw [CommonField.source_exact,value_exact]

def recoverComputes : Computes (CommonField.presentation G u v U V).encoding (encoding G u v)
    (embedding G u v U V).toLinearMap.leftInverse :=
  FieldCodec.retractComputes (presentation G u v) (CommonField.presentation G u v U V)
    (embedding G u v U V)

def post (z : List (OriginalField.field G) × FieldReduction.Context (CommonField.field G u v U V)) :
    field G u v := (embedding G u v U V).toLinearMap.leftInverse (OriginalTarget.post G u v U V z)

def postComputes : Computes
    (OracleBatch.contextEncoding (OriginalField.encoding G)
      (FieldReduction.contextEncoding (CommonField.presentation G u v U V)))
    (encoding G u v) (post G u v U V) :=
  (OriginalTarget.postComputes G u v U V).andThen (recoverComputes G u v U V)

theorem recovery (r : OriginalQuery.UnaryInput (s:=s) (arity:=arity)) :
    value G u v r = post G u v U V
      (OracleBatch.answers (OriginalField.value G) (OriginalTarget.pre G u v U V r)) := by
  unfold post
  rw [← OriginalTarget.recovery, common_value, FieldCodec.retract_embedding]

def reduction : PolyTimeOracleReduction
    (FieldReduction.inputEncoding (s:=s) (arity:=arity)) (encoding G u v)
    (FieldReduction.queryEncoding (s:=s) (arity:=arity)) (OriginalField.encoding G)
    (value G u v) (OriginalField.value G) :=
  OracleBatch.of_eq (OriginalTarget.preComputes G u v U V) (postComputes G u v U V)
    ((OriginalField.tables G).outputBound (OriginalField.presentation G)) (value G u v)
    (recovery G u v U V)

theorem run_trace (oracle : List Bool → List Bool)
    (ho : RepresentsOracle (FieldReduction.queryEncoding (s:=s) (arity:=arity)) (OriginalField.encoding G)
      (OriginalField.value G) oracle) (r : OriginalQuery.UnaryInput (s:=s) (arity:=arity)) :
    ∃ t ≤ (reduction G u v U V).time.eval ((FieldReduction.inputEncoding (s:=s) (arity:=arity)).encode r).length,
      OracleBatch.RunsTrace (reduction G u v U V).machine oracle
        ((reduction G u v U V).machine.init ((FieldReduction.inputEncoding (s:=s) (arity:=arity)).encode r))
        ((reduction G u v U V).machine.output ((encoding G u v).encode (value G u v r))) t
        [(FieldReduction.queryEncoding (s:=s) (arity:=arity)).encode (OriginalTarget.query G u v U V r)] := by
  have h := OracleBatch.of_eq_run_trace (OriginalTarget.preComputes G u v U V) (postComputes G u v U V)
      ((OriginalField.tables G).outputBound (OriginalField.presentation G)) (value G u v)
      (recovery G u v U V) oracle ho r
  simp only [OriginalTarget.pre,FieldReduction.pre,List.map_cons,List.map_nil] at h
  exact h

def controlled : LengthControlledOracleReduction
    (FieldReduction.inputEncoding (s:=s) (arity:=arity)) (encoding G u v)
    (FieldReduction.queryEncoding (s:=s) (arity:=arity)) (OriginalField.encoding G)
    (value G u v) (OriginalField.value G) where
  reduction := reduction G u v U V
  targetOutput := (OriginalField.tables G).outputBound (OriginalField.presentation G)
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

def primitivePolynomial : Polynomial ℕ :=
  Polynomial.C (reduction G u v U V).machine.primitiveBudget * (reduction G u v U V).time

theorem execution (oracle : List Bool → List Bool)
    (ho : RepresentsOracle (FieldReduction.queryEncoding (s:=s) (arity:=arity)) (OriginalField.encoding G)
      (OriginalField.value G) oracle) (r : OriginalQuery.UnaryInput (s:=s) (arity:=arity)) :
    ∃ t ≤ (reduction G u v U V).time.eval ((FieldReduction.inputEncoding (s:=s) (arity:=arity)).encode r).length,
      OracleBatch.RunsTrace (reduction G u v U V).machine oracle
        ((reduction G u v U V).machine.init ((FieldReduction.inputEncoding (s:=s) (arity:=arity)).encode r))
        ((reduction G u v U V).machine.output ((encoding G u v).encode (value G u v r))) t
        [(FieldReduction.queryEncoding (s:=s) (arity:=arity)).encode (OriginalTarget.query G u v U V r)] ∧
      queryCount (reduction G u v U V).machine oracle
        ((reduction G u v U V).machine.init ((FieldReduction.inputEncoding (s:=s) (arity:=arity)).encode r)) t = 1 ∧
      OracleBatch.primitiveCount (reduction G u v U V).machine oracle
        ((reduction G u v U V).machine.init ((FieldReduction.inputEncoding (s:=s) (arity:=arity)).encode r)) t ≤
        (primitivePolynomial G u v U V).eval ((FieldReduction.inputEncoding (s:=s) (arity:=arity)).encode r).length := by
  obtain ⟨t,ht,hr⟩ := run_trace G u v U V oracle ho r
  refine ⟨t,ht,hr,?_,?_⟩
  · simpa using hr.count
  · exact (OracleBatch.primitiveCount_le _ _ _ _).trans (by
      simpa only [primitivePolynomial,Polynomial.eval_mul,Polynomial.eval_C] using
        Nat.mul_le_mul_left (reduction G u v U V).machine.primitiveBudget ht)

end Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.Composition.SourceCodec
