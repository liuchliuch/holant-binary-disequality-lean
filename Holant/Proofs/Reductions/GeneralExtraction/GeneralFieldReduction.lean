import Holant.Proofs.Reductions.GeneralExtraction.GeneralPreparation
import Holant.Proofs.Reductions.GeneralExtraction.GeneralOriginalQuery
import Holant.Proofs.BinaryInterpolation.SingularExtraction.FieldReduction
import Holant.Proofs.Algorithms.TraceQueryControl


noncomputable section
attribute [local instance] Classical.propDecidable
namespace Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralFieldReduction
open Holant.Algebraic Holant.Complexity Computability BinaryCompose
open FixedFieldMachines GraphPreprocessing RawClosedNetwork
open FixedGadgetSubstitution FixedGadgetSubstitution.Compiler
open Holant.Complexity.UniversalPairReduction.Surgery
open Holant.LocalDrafts.BinaryInterpolation.SingularExtraction
open GeneralPowerExposure
variable {K : Type} [Field K] [Algebra ℚ K] {d s : ℕ} {arity : ℕ → ℕ}
variable (F : FixedField K d) (G : (i : Fin s) → Signature K (arity i.val))
variable (f : Signature K (arity s)) (P : PowerMacro G f)

abbrev Input := GeneralOriginalQuery.Input (s:=s) (arity:=arity)
abbrev inputEncoding := validatedEncoding (s+1) 1 arity
abbrev queryEncoding := validatedEncoding s 1 arity
abbrev macroArity := sourceArity (GeneralOriginalQuery.templates G f P)
abbrev targetTables := FieldReduction.targetTables F G

def grouped (r : Input (s:=s) (arity:=arity)) :
    ResidueAnchors.Input (s+1) 1 (macroArity G f P) :=
  let t := GeneralPreparation.grouped (GeneralOriginalQuery.factorTable G f)
    s P.exponent P.positive (by omega) r
  ⟨t.val, by rw [macroArity, GeneralOriginalQuery.sourceArity_eq]; exact t.property⟩

def groupedComputes : Computes (inputEncoding (s:=s) (arity:=arity))
    (validatedEncoding (s+1) 1 (macroArity G f P)) (grouped G f P) :=
  recode (GeneralPreparation.computes (GeneralOriginalQuery.factorTable G f)
    s P.exponent P.positive (by omega)) id (fun _ => rfl) (fun _ => rfl)

def query (r : Input (s:=s) (arity:=arity)) : ResidueAnchors.Input s 1 arity :=
  Compiler.value (s+1) 1 (macroArity G f P) (GeneralOriginalQuery.templates G f P)
    s arity (fun i hi => ⟨GeneralOriginalQuery.templates_valid G f P i hi, rfl⟩) (grouped G f P r)

def queryComputes : Computes (inputEncoding (s:=s) (arity:=arity))
    (queryEncoding (s:=s) (arity:=arity)) (query G f P) :=
  (groupedComputes G f P).andThen
    (Compiler.computes (s+1) 1 (macroArity G f P) (GeneralOriginalQuery.templates G f P)
      s arity (fun i hi => ⟨GeneralOriginalQuery.templates_valid G f P i hi, rfl⟩))

theorem grouped_live (r : Input (s:=s) (arity:=arity)) (h : GeneralOriginalQuery.IsLive G f P r) :
    (grouped G f P r).val = GeneralOriginalQuery.grouped G f P r h :=
  GeneralPreparation.grouped_live (GeneralOriginalQuery.factorTable G f)
    s P.exponent P.positive (by omega) r h

theorem query_live (r : Input (s:=s) (arity:=arity)) (h : GeneralOriginalQuery.IsLive G f P r) :
    query G f P r = GeneralOriginalQuery.emitted G f P r h := by
  apply Subtype.ext
  exact congrArg (replace (GeneralOriginalQuery.templates G f P)) (grouped_live G f P r h)

theorem grouped_dead (r : Input (s:=s) (arity:=arity)) (h : ¬ GeneralOriginalQuery.IsLive G f P r) :
    (grouped G f P r).val = ⟨[], []⟩ :=
  GeneralPreparation.grouped_dead (GeneralOriginalQuery.factorTable G f)
    s P.exponent P.positive (by omega) r h

theorem query_dead (r : Input (s:=s) (arity:=arity)) (h : ¬ GeneralOriginalQuery.IsLive G f P r) :
    (query G f P r).val = ⟨[], []⟩ := by
  change replace (GeneralOriginalQuery.templates G f P) (grouped G f P r).val = _
  rw [grouped_dead G f P r h]
  rfl

def classCoefficient (ρ : Fin P.exponent × Fin 1) : K :=
  if ResidueAnchors.Live (s:=s+1) (b:=1) (arity:=arity) (GeneralOriginalQuery.factorTable G f)
      s s P.exponent 1 P.positive (by omega) ρ then
    (ResidueAnchors.value (GeneralOriginalQuery.factorTable G f)
      (ResidueAnchors.anchor (s:=s+1) (b:=1) (arity:=arity) (GeneralOriginalQuery.factorTable G f)
        s s P.exponent 1 P.positive (by omega) ρ))⁻¹ else 0

def coefficient (r : Input (s:=s) (arity:=arity)) : K :=
  classCoefficient G f P (ResidueAnchors.residue s s P.exponent 1 P.positive (by omega) r)

def coefficientComputes : Computes (inputEncoding (s:=s) (arity:=arity)) F.encoding (coefficient G f P) :=
  (ResidueMachine.graphResiduesComputes P.exponent P.positive s s 1 (by omega)
    (ResidueMachine.finEncoding P.exponent) (ResidueMachine.finEncoding 1)).andThen
      (FiniteRecode.computes (ResidueMachine.residueEncoding P.exponent 1) F.encoding
        (classCoefficient G f P) (2*P.exponent+1+1) (ResidueMachine.residueEncoding_length P.exponent 1))

abbrev Context (K : Type) := K × ℕ
def contextEncoding := pairEncoding F.encoding UnaryBinary.unaryEncoding
def context (r : Input (s:=s) (arity:=arity)) : Context K :=
  (coefficient G f P r, occurrences s (grouped G f P r).val)

def contextComputes : Computes (inputEncoding (s:=s) (arity:=arity)) (contextEncoding F) (context G f P) :=
  pairComputes (coefficientComputes F G f P)
    ((groupedComputes G f P).andThen (occurrencesComputes (s+1) 1 (macroArity G f P) s))

def correction (p : K × Context K) : K := p.1 * (P.scale⁻¹)^p.2.2 * p.2.1

def correctionComputes : Computes (pairEncoding F.encoding (contextEncoding F)) F.encoding
    (correction G f P) := by
  let ctx := Wiring.secondComputes F.encoding (contextEncoding F)
  let count := ctx.andThen (Wiring.secondComputes F.encoding UnaryBinary.unaryEncoding)
  let coeff := ctx.andThen (Wiring.firstComputes F.encoding UnaryBinary.unaryEncoding)
  let scaled := (pairComputes (Wiring.firstComputes F.encoding (contextEncoding F)) count).andThen
    (ScalarPower.correction F P.scale)
  exact (pairComputes scaled coeff).andThen (Concrete.fieldMultiplication F)

def pre (r : Input (s:=s) (arity:=arity)) := ([query G f P r], context G f P r)
def preComputes : Computes (inputEncoding (s:=s) (arity:=arity))
    (OracleBatch.contextEncoding (queryEncoding (s:=s) (arity:=arity)) (contextEncoding F)) (pre G f P) :=
  pairComputes (fixedListComputes (inputEncoding (s:=s) (arity:=arity))
    (queryEncoding (s:=s) (arity:=arity)) (fun r (_ : Unit) => query G f P r)
      (fun _ => queryComputes G f P) [()]) (contextComputes F G f P)

def post (p : List K × Context K) : K := correction G f P (p.1.getD 0 0, p.2)
def postComputes : Computes (OracleBatch.contextEncoding F.encoding (contextEncoding F)) F.encoding (post G f P) :=
  (pairComputes ((Wiring.firstComputes (framedListEncoding F.encoding) (contextEncoding F)).andThen
    (getDComputes F.encoding 0 0))
    (Wiring.secondComputes (framedListEncoding F.encoding) (contextEncoding F))).andThen
      (correctionComputes F G f P)

def sourceValue (r : Input (s:=s) (arity:=arity)) : K :=
  ResidueAnchors.value (GeneralOriginalQuery.factorTable G f) r

theorem cancel (a c y : K) (ha : a ≠ 0) (hc : c ≠ 0) (n : ℕ) :
    (a^n*c*y)*(a⁻¹)^n*c⁻¹ = y := by
  calc
    _ = (a^n*(a⁻¹)^n)*(c*c⁻¹)*y := by ring
    _ = y := by rw [← mul_pow, mul_inv_cancel₀ ha, mul_inv_cancel₀ hc]; simp

theorem recovery (r : Input (s:=s) (arity:=arity)) :
    sourceValue G f r = post G f P (OracleBatch.answers ((targetTables F G).evaluate F) (pre G f P r)) := by
  change _ = correction G f P ((targetTables F G).evaluate F (query G f P r), context G f P r)
  by_cases h : GeneralOriginalQuery.IsLive G f P r
  · have hq : (targetTables F G).evaluate F (query G f P r) =
        GeneralOriginalQuery.normalization G f P r h * sourceValue G f r := by
      rw [FieldReduction.target_evaluate, query_live G f P r h]
      exact GeneralOriginalQuery.emitted_value G f P r h
    change ResidueAnchors.Live _ _ _ _ _ _ _ _ at h
    have hc : coefficient G f P r =
        (GeneralResidueQuery.scale (Choice.table G) s P.exponent P.positive f r)⁻¹ := by
      simp only [coefficient, classCoefficient, if_pos h, GeneralResidueQuery.scale]
    have hn := GeneralResidueQuery.scale_nonzero (Choice.table G) s P.exponent P.positive f r h
    simp only [correction, context, hq, hc, grouped_live G f P r h, GeneralOriginalQuery.normalization]
    exact (cancel _ _ _ P.scale_ne_zero hn _).symm
  · have hz := ResidueAnchors.dead_value (GeneralOriginalQuery.factorTable G f)
      s s P.exponent 1 P.positive (by omega) r h
    change ¬ ResidueAnchors.Live _ _ _ _ _ _ _ _ at h
    have hc : coefficient G f P r = 0 := by simp only [coefficient, classCoefficient, if_neg h]
    simp only [sourceValue, hz, correction, context, hc, mul_zero]

/-- Actual finite oracle machine on the original input codec. -/
def reduction : PolyTimeOracleReduction (inputEncoding (s:=s) (arity:=arity)) F.encoding
    (queryEncoding (s:=s) (arity:=arity)) F.encoding (sourceValue G f) ((targetTables F G).evaluate F) :=
  OracleBatch.of_eq (preComputes F G f P) (postComputes F G f P)
    ((targetTables F G).outputBound F) (sourceValue G f) (recovery F G f P)

/-- Query safety is obtained from the ACTUAL completed transcript. It is
not an assumed promise about the preprocessor or the oracle. -/
def controlled : LengthControlledOracleReduction (inputEncoding (s:=s) (arity:=arity)) F.encoding
    (queryEncoding (s:=s) (arity:=arity)) F.encoding (sourceValue G f) ((targetTables F G).evaluate F) := by
  have he : sourceValue G f = fun r =>
      post G f P (OracleBatch.answers ((targetTables F G).evaluate F) (pre G f P r)) := funext (recovery F G f P)
  rw [he]
  exact Holant.LocalDrafts.MainChain.TraceQueryControl.controlledBatch
    (preComputes F G f P) (postComputes F G f P) ((targetTables F G).outputBound F)

def timePolynomial : Polynomial ℕ :=
  let a := preComputes F G f P
  let b := postComputes F G f P
  let size := (targetTables F G).outputBound F
  a.time + 16*(a.outputBound.bound + OracleBatch.decoderBound a size + 1) +
    b.time.comp (OracleBatch.decoderBound a size)

theorem reduction_time : (reduction F G f P).time = timePolynomial F G f P := rfl

theorem run_trace (oracle : List Bool → List Bool)
    (ho : RepresentsOracle (queryEncoding (s:=s) (arity:=arity)) F.encoding
      ((targetTables F G).evaluate F) oracle) (r : Input (s:=s) (arity:=arity)) :
    ∃ t ≤ (timePolynomial F G f P).eval ((inputEncoding (s:=s) (arity:=arity)).encode r).length,
      OracleBatch.RunsTrace (reduction F G f P).machine oracle
        ((reduction F G f P).machine.init ((inputEncoding (s:=s) (arity:=arity)).encode r))
        ((reduction F G f P).machine.output (F.encoding.encode (sourceValue G f r)))
        t [(queryEncoding (s:=s) (arity:=arity)).encode (query G f P r)] := by
  have h := OracleBatch.of_eq_run_trace (preComputes F G f P) (postComputes F G f P)
      ((targetTables F G).outputBound F) (sourceValue G f) (recovery F G f P) oracle ho r
  simp only [pre, List.map_cons, List.map_nil] at h
  exact h

end Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralFieldReduction
