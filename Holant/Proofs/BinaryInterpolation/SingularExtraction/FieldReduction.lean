import Holant.Proofs.BinaryInterpolation.SingularExtraction.Preparation
import Holant.Proofs.BinaryInterpolation.SingularExtraction.OriginalQuery
import Holant.Complexity.FixedGadgetSubstitution.Compiler.Compile
import Holant.Complexity.FixedFieldMachines.ScalarPower.Correction
import Holant.Complexity.EncodedHolantOutputSize
import Holant.Complexity.OracleBatch.ReductionTrace


noncomputable section
attribute [local instance] Classical.propDecidable
namespace Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.FieldReduction
open Holant Holant.Algebraic Holant.Complexity Computability BinaryCompose
open FixedFieldMachines GraphPreprocessing RawClosedNetwork
open FixedGadgetSubstitution FixedGadgetSubstitution.Compiler
open Holant.Complexity.UniversalPairReduction.Surgery
open Holant.Complexity.UniversalPairReduction.ThreeQuery
set_option backward.isDefEq.respectTransparency false
variable {K : Type} [Field K] [Algebra ℚ K] {n s : ℕ} {arity : ℕ → ℕ}
variable (F : FixedField K n) (G : (i : Fin s) → Signature K (arity i.val))
variable (u v : Bool → K) (U : PowerMacro G u) (V : PowerMacro G v)

abbrev Input := OriginalQuery.UnaryInput (s:=s) (arity:=arity)
abbrev inputEncoding := validatedEncoding (s+2) 1 (Tables.adjoinedArity s arity 1 1)
abbrev queryEncoding := validatedEncoding s 1 arity
abbrev macroArity := sourceArity (OriginalQuery.templates G u v U V)

def grouped (r : Input (s:=s) (arity:=arity)) :
    ResidueAnchors.Input (s+2) 1 (macroArity G u v U V) :=
  let t := Preparation.grouped (Tables.familyTable G u v) s (s+1) U.exponent V.exponent
    U.positive V.positive (by omega) (by omega) (by omega)
    (by simp [Tables.adjoinedArity]) (by simp [Tables.adjoinedArity]) r
  ⟨t.val, by
    rw [macroArity, OriginalQuery.sourceArity_eq, ← Tables.changed_adjoined]
    exact t.property⟩

def groupedComputes : Computes (inputEncoding (s:=s) (arity:=arity))
    (validatedEncoding (s+2) 1 (macroArity G u v U V)) (grouped G u v U V) :=
  recode (Preparation.computes (Tables.familyTable G u v) s (s+1) U.exponent V.exponent
    U.positive V.positive (by omega) (by omega) (by omega)
    (by simp [Tables.adjoinedArity]) (by simp [Tables.adjoinedArity]))
      id (fun _ => rfl) (fun _ => rfl)

def query (r : Input (s:=s) (arity:=arity)) : ResidueAnchors.Input s 1 arity :=
  Compiler.value (s+2) 1 (macroArity G u v U V) (OriginalQuery.templates G u v U V)
    s arity (fun i hi => ⟨OriginalQuery.templates_valid G u v U V i hi, rfl⟩)
    (grouped G u v U V r)

def queryComputes : Computes (inputEncoding (s:=s) (arity:=arity))
    (queryEncoding (s:=s) (arity:=arity)) (query G u v U V) :=
  (groupedComputes G u v U V).andThen
    (Compiler.computes (s+2) 1 (macroArity G u v U V) (OriginalQuery.templates G u v U V)
      s arity (fun i hi => ⟨OriginalQuery.templates_valid G u v U V i hi, rfl⟩))

theorem grouped_live (r : Input (s:=s) (arity:=arity)) (h : OriginalQuery.IsLive G u v U V r) :
    (grouped G u v U V r).val = OriginalQuery.grouped G u v U V r :=
  Preparation.grouped_live (Tables.familyTable G u v) s (s+1) U.exponent V.exponent
    U.positive V.positive (by omega) (by omega) (by omega)
    (by simp [Tables.adjoinedArity]) (by simp [Tables.adjoinedArity]) r h

theorem query_live (r : Input (s:=s) (arity:=arity)) (h : OriginalQuery.IsLive G u v U V r) :
    (query G u v U V r).val = OriginalQuery.emitted G u v U V r :=
  congrArg (replace (OriginalQuery.templates G u v U V)) (grouped_live G u v U V r h)

theorem grouped_dead (r : Input (s:=s) (arity:=arity)) (h : ¬ OriginalQuery.IsLive G u v U V r) :
    (grouped G u v U V r).val = ⟨[],[]⟩ :=
  Preparation.grouped_dead (Tables.familyTable G u v) s (s+1) U.exponent V.exponent
    U.positive V.positive (by omega) (by omega) (by omega)
    (by simp [Tables.adjoinedArity]) (by simp [Tables.adjoinedArity]) r h

theorem query_dead (r : Input (s:=s) (arity:=arity)) (h : ¬ OriginalQuery.IsLive G u v U V r) :
    (query G u v U V r).val = ⟨[],[]⟩ := by
  change replace (OriginalQuery.templates G u v U V) (grouped G u v U V r).val = _
  rw [grouped_dead G u v U V r h]
  rfl

def targetTables : ExactSignatureTables n s 1 arity where
  vertex i x := F.decode.symm (G i x)
  edge _ a b := F.decode.symm (Signature.disequality a b)

theorem target_evaluate (q : ResidueAnchors.Input s 1 arity) :
    (targetTables F G).evaluate F q =
      (q.val.realize q.property G (fun _ => Signature.disequality)).denote Fin.elim0 := by
  rw [ExactSignatureTables.evaluate_eq_decoded]
  simp only [targetTables, LinearEquiv.apply_symm_apply]

def classCoefficient (ρ : Fin U.exponent × Fin V.exponent) : K :=
  if ResidueAnchors.Live (s:=s+2) (b:=1) (arity:=Tables.adjoinedArity s arity 1 1)
      (Tables.familyTable G u v) s (s+1) U.exponent V.exponent U.positive V.positive ρ
  then (ResidueAnchors.value (Tables.familyTable G u v)
    (ResidueAnchors.anchor (s:=s+2) (b:=1) (arity:=Tables.adjoinedArity s arity 1 1)
      (Tables.familyTable G u v) s (s+1) U.exponent V.exponent U.positive V.positive ρ))⁻¹
  else 0

def coefficient (r : Input (s:=s) (arity:=arity)) : K :=
  classCoefficient G u v U V
    (ResidueAnchors.residue s (s+1) U.exponent V.exponent U.positive V.positive r)

def coefficientComputes : Computes (inputEncoding (s:=s) (arity:=arity)) F.encoding
    (coefficient G u v U V) :=
  (ResidueMachine.graphResiduesComputes U.exponent U.positive s (s+1) V.exponent V.positive
    (ResidueMachine.finEncoding U.exponent) (ResidueMachine.finEncoding V.exponent)).andThen
      (FiniteRecode.computes (ResidueMachine.residueEncoding U.exponent V.exponent)
        F.encoding (classCoefficient G u v U V) (2*U.exponent+1+V.exponent)
        (ResidueMachine.residueEncoding_length U.exponent V.exponent))

abbrev Context (K : Type) := K × (ℕ × ℕ)
def contextEncoding := pairEncoding F.encoding
  (pairEncoding UnaryBinary.unaryEncoding UnaryBinary.unaryEncoding)
def context (r : Input (s:=s) (arity:=arity)) : Context K :=
  (coefficient G u v U V r, (occurrences s (grouped G u v U V r).val,
    occurrences (s+1) (grouped G u v U V r).val))

def contextComputes : Computes (inputEncoding (s:=s) (arity:=arity)) (contextEncoding F)
    (context G u v U V) :=
  pairComputes (coefficientComputes F G u v U V)
    ((groupedComputes G u v U V).andThen
      (pairComputes (occurrencesComputes (s+2) 1 (macroArity G u v U V) s)
        (occurrencesComputes (s+2) 1 (macroArity G u v U V) (s+1))))

def correction (p : K × Context K) : K :=
  p.1 * (U.scale⁻¹)^p.2.2.1 * (V.scale⁻¹)^p.2.2.2 * p.2.1

/-- Three actual field multiplications/power programs; projections operate on
framed tapes. No semantic arithmetic is counted as a machine step. -/
def correctionComputes : Computes (pairEncoding F.encoding (contextEncoding F)) F.encoding
    (correction G u v U V) := by
  let ctx := Wiring.secondComputes F.encoding (contextEncoding F)
  let counts := ctx.andThen (Wiring.secondComputes F.encoding
    (pairEncoding UnaryBinary.unaryEncoding UnaryBinary.unaryEncoding))
  let m := counts.andThen (Wiring.firstComputes UnaryBinary.unaryEncoding UnaryBinary.unaryEncoding)
  let n := counts.andThen (Wiring.secondComputes UnaryBinary.unaryEncoding UnaryBinary.unaryEncoding)
  let d := ctx.andThen (Wiring.firstComputes F.encoding
    (pairEncoding UnaryBinary.unaryEncoding UnaryBinary.unaryEncoding))
  let first := (pairComputes (Wiring.firstComputes F.encoding (contextEncoding F)) m).andThen
    (ScalarPower.correction F U.scale)
  let second := (pairComputes first n).andThen (ScalarPower.correction F V.scale)
  exact (pairComputes second d).andThen (Concrete.fieldMultiplication F)

def pre (r : Input (s:=s) (arity:=arity)) := ([query G u v U V r], context G u v U V r)
def preComputes : Computes (inputEncoding (s:=s) (arity:=arity))
    (OracleBatch.contextEncoding (queryEncoding (s:=s) (arity:=arity)) (contextEncoding F))
    (pre G u v U V) :=
  pairComputes
    (fixedListComputes (inputEncoding (s:=s) (arity:=arity)) (queryEncoding (s:=s) (arity:=arity))
      (fun r (_ : Unit) => query G u v U V r) (fun _ => queryComputes G u v U V) [()])
    (contextComputes F G u v U V)

def post (p : List K × Context K) : K := correction G u v U V (p.1.getD 0 0,p.2)
def postComputes : Computes (OracleBatch.contextEncoding F.encoding (contextEncoding F)) F.encoding
    (post G u v U V) :=
  (pairComputes
    ((Wiring.firstComputes (framedListEncoding F.encoding) (contextEncoding F)).andThen
      (getDComputes F.encoding 0 0))
    (Wiring.secondComputes (framedListEncoding F.encoding) (contextEncoding F))).andThen
      (correctionComputes F G u v U V)

def sourceValue (r : Input (s:=s) (arity:=arity)) : K :=
  ResidueAnchors.value (Tables.familyTable G u v) r

theorem cancel (a b d y : K) (ha : a ≠ 0) (hb : b ≠ 0) (hd : d ≠ 0) (m n : ℕ) :
    (a^m*b^n*d*y)*(a⁻¹)^m*(b⁻¹)^n*d⁻¹ = y := by
  calc
    _ = (a^m*(a⁻¹)^m)*(b^n*(b⁻¹)^n)*(d*d⁻¹)*y := by ring
    _ = y := by
      rw [← mul_pow, ← mul_pow, mul_inv_cancel₀ ha, mul_inv_cancel₀ hb, mul_inv_cancel₀ hd]
      simp

theorem recovery (r : Input (s:=s) (arity:=arity)) :
    sourceValue G u v r = post G u v U V
      (OracleBatch.answers ((targetTables F G).evaluate F) (pre G u v U V r)) := by
  change _ = correction G u v U V ((targetTables F G).evaluate F (query G u v U V r),
    context G u v U V r)
  by_cases h : OriginalQuery.IsLive G u v U V r
  · have hq : (targetTables F G).evaluate F (query G u v U V r) =
        OriginalQuery.normalization G u v U V r * sourceValue G u v r := by
      rw [target_evaluate]
      have he : query G u v U V r =
          ⟨OriginalQuery.emitted G u v U V r, OriginalQuery.emitted_valid G u v U V r h⟩ :=
        Subtype.ext (query_live G u v U V r h)
      rw [he]
      exact OriginalQuery.emitted_value G u v U V r h
    change ResidueAnchors.Live _ _ _ _ _ _ _ _ at h
    have hc : coefficient G u v U V r = (OriginalQuery.anchorScalar G u v U V r)⁻¹ := by
      simp only [coefficient, classCoefficient, if_pos h, OriginalQuery.anchorScalar]
    have hd : OriginalQuery.anchorScalar G u v U V r ≠ 0 :=
      ResidueAnchors.anchor_nonzero (Tables.familyTable G u v) s (s+1) U.exponent V.exponent
        U.positive V.positive _ h
    simp only [correction, context, hq, hc, grouped_live G u v U V r h,
      OriginalQuery.normalization]
    exact (cancel _ _ _ _ U.scale_ne_zero V.scale_ne_zero hd _ _).symm
  · have hz := OriginalQuery.dead G u v U V r h
    change ¬ ResidueAnchors.Live _ _ _ _ _ _ _ _ at h
    have hc : coefficient G u v U V r = 0 := by
      simp only [coefficient, classCoefficient, if_neg h]
    simp only [sourceValue, hz, correction, context, hc, mul_zero]

/-- The actual finite oracle program, constructed rather than supplied. -/
def reduction : PolyTimeOracleReduction (inputEncoding (s:=s) (arity:=arity)) F.encoding
    (queryEncoding (s:=s) (arity:=arity)) F.encoding (sourceValue G u v)
    ((targetTables F G).evaluate F) :=
  OracleBatch.of_eq (preComputes F G u v U V) (postComputes F G u v U V)
    ((targetTables F G).outputBound F) (sourceValue G u v) (recovery F G u v U V)

/-- One polynomial of the ORIGINAL input length; answer lengths are included
through the original-family ExactSignatureTables output bound. -/
def timePolynomial : Polynomial ℕ :=
  let a := preComputes F G u v U V
  let b := postComputes F G u v U V
  let size := (targetTables F G).outputBound F
  a.time + 16*(a.outputBound.bound + OracleBatch.decoderBound a size + 1) +
    b.time.comp (OracleBatch.decoderBound a size)

theorem reduction_time : (reduction F G u v U V).time = timePolynomial F G u v U V := rfl

def primitivePolynomial : Polynomial ℕ :=
  Polynomial.C (reduction F G u v U V).machine.primitiveBudget * timePolynomial F G u v U V

theorem run_cost (oracle : List Bool → List Bool)
    (ho : RepresentsOracle (queryEncoding (s:=s) (arity:=arity)) F.encoding
      ((targetTables F G).evaluate F) oracle) (r : Input (s:=s) (arity:=arity)) :
    ∃ t ≤ (timePolynomial F G u v U V).eval ((inputEncoding (s:=s) (arity:=arity)).encode r).length,
      (fun p => p.bind ((reduction F G u v U V).machine.step oracle))^[t]
        (some ((reduction F G u v U V).machine.init ((inputEncoding (s:=s) (arity:=arity)).encode r))) =
        some ((reduction F G u v U V).machine.output (F.encoding.encode (sourceValue G u v r))) ∧
      queryCount (reduction F G u v U V).machine oracle
        ((reduction F G u v U V).machine.init ((inputEncoding (s:=s) (arity:=arity)).encode r)) t = 1 ∧
      OracleBatch.primitiveCount (reduction F G u v U V).machine oracle
        ((reduction F G u v U V).machine.init ((inputEncoding (s:=s) (arity:=arity)).encode r)) t ≤
        (primitivePolynomial F G u v U V).eval ((inputEncoding (s:=s) (arity:=arity)).encode r).length := by
  have h := OracleBatch.reduction_query_count (preComputes F G u v U V) (postComputes F G u v U V)
      ((targetTables F G).outputBound F) oracle ho r
  have he := recovery F G u v U V r
  rw [← he] at h
  simp only [pre, List.length_cons, List.length_nil] at h
  exact h

/-- The sole query is the actual serialized physical expansion, not just an
abstract call count. This includes the explicitly proved dead/empty branch. -/
theorem run_trace (oracle : List Bool → List Bool)
    (ho : RepresentsOracle (queryEncoding (s:=s) (arity:=arity)) F.encoding
      ((targetTables F G).evaluate F) oracle) (r : Input (s:=s) (arity:=arity)) :
    ∃ t ≤ (timePolynomial F G u v U V).eval ((inputEncoding (s:=s) (arity:=arity)).encode r).length,
      OracleBatch.RunsTrace (reduction F G u v U V).machine oracle
        ((reduction F G u v U V).machine.init ((inputEncoding (s:=s) (arity:=arity)).encode r))
        ((reduction F G u v U V).machine.output (F.encoding.encode (sourceValue G u v r)))
        t [(queryEncoding (s:=s) (arity:=arity)).encode (query G u v U V r)] := by
  have h := OracleBatch.of_eq_run_trace (preComputes F G u v U V) (postComputes F G u v U V)
      ((targetTables F G).outputBound F) (sourceValue G u v) (recovery F G u v U V) oracle ho r
  simp only [pre, List.map_cons, List.map_nil] at h
  exact h

def queryPolynomial : Polynomial ℕ := (queryComputes G u v U V).outputBound.bound
def answerPolynomial : Polynomial ℕ :=
  ((targetTables F G).outputBound F).bound.comp (queryPolynomial G u v U V)

theorem query_length (r : Input (s:=s) (arity:=arity)) :
    ((queryEncoding (s:=s) (arity:=arity)).encode (query G u v U V r)).length ≤
      (queryPolynomial G u v U V).eval ((inputEncoding (s:=s) (arity:=arity)).encode r).length :=
  (queryComputes G u v U V).outputBound.length_le r

theorem answer_length (r : Input (s:=s) (arity:=arity)) :
    (F.encoding.encode ((targetTables F G).evaluate F (query G u v U V r))).length ≤
      (answerPolynomial F G u v U V).eval ((inputEncoding (s:=s) (arity:=arity)).encode r).length := by
  apply le_trans (((targetTables F G).outputBound F).length_le (query G u v U V r))
  simpa only [answerPolynomial, Polynomial.eval_comp] using
    natPolynomial_eval_mono ((targetTables F G).outputBound F).bound (query_length G u v U V r)

/-- One fixed polynomial simultaneously dominates transitions, primitives,
query bytes and answer bytes, all at the original encoded input length. -/
def budget : Polynomial ℕ := timePolynomial F G u v U V + primitivePolynomial F G u v U V +
  queryPolynomial G u v U V + answerPolynomial F G u v U V + 1

theorem bounded_run (oracle : List Bool → List Bool)
    (ho : RepresentsOracle (queryEncoding (s:=s) (arity:=arity)) F.encoding
      ((targetTables F G).evaluate F) oracle) (r : Input (s:=s) (arity:=arity)) :
    ∃ t ≤ (budget F G u v U V).eval ((inputEncoding (s:=s) (arity:=arity)).encode r).length,
      (fun p => p.bind ((reduction F G u v U V).machine.step oracle))^[t]
        (some ((reduction F G u v U V).machine.init ((inputEncoding (s:=s) (arity:=arity)).encode r))) =
        some ((reduction F G u v U V).machine.output (F.encoding.encode (sourceValue G u v r))) ∧
      queryCount (reduction F G u v U V).machine oracle
        ((reduction F G u v U V).machine.init ((inputEncoding (s:=s) (arity:=arity)).encode r)) t = 1 ∧
      OracleBatch.primitiveCount (reduction F G u v U V).machine oracle
        ((reduction F G u v U V).machine.init ((inputEncoding (s:=s) (arity:=arity)).encode r)) t ≤
        (budget F G u v U V).eval ((inputEncoding (s:=s) (arity:=arity)).encode r).length ∧
      ((queryEncoding (s:=s) (arity:=arity)).encode (query G u v U V r)).length ≤
        (budget F G u v U V).eval ((inputEncoding (s:=s) (arity:=arity)).encode r).length ∧
      (F.encoding.encode ((targetTables F G).evaluate F (query G u v U V r))).length ≤
        (budget F G u v U V).eval ((inputEncoding (s:=s) (arity:=arity)).encode r).length := by
  obtain ⟨t, ht, hr, hq, hp⟩ := run_cost F G u v U V oracle ho r
  have hquery := query_length G u v U V r
  have hanswer := answer_length F G u v U V r
  refine ⟨t, ?_, hr, hq, ?_, ?_, ?_⟩ <;>
    simp only [budget, Polynomial.eval_add, Polynomial.eval_one] <;> omega

end Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.FieldReduction
