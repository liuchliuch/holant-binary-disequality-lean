import Holant.Proofs.Hardness.GeneralEOTensorPowerRemovalPadding
import Holant.Proofs.Algorithms.FieldTransport
import Holant.Proofs.Algorithms.TraceQueryControl
import Holant.Complexity.OracleBatch.ReductionTrace
import Holant.Complexity.EncodedHolantOutputSize

/-! The actual one-query counting programme for arbitrary fixed tensor-power
removal. Source and target have separate faithful number-field codecs. Only the
literal target coefficient embedding is required; f need not belong to the
target field. All finite residue constants, graph operations and answer
arithmetic compile into finite Boolean-stack machines. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOTensorPowerRemovalReduction
open Turing Computability Holant Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines FixedGadgetSubstitution.Compiler
open UniversalPairReduction.Surgery GeneralEOTensorPowerRemovalRaw GeneralEOTensorPowerRemovalValue
open Holant.LocalDrafts.MainChain
namespace P
export GeneralEOTensorPowerRemovalPadding (Input inputEncoding value residue residueComputes
  coefficient query queryComputes recover)
end P
namespace T
export GeneralEOTensorPowerRemovalTables (signatures denote)
end T
namespace R
export Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.ResidueMachine (computes)
end R
set_option backward.isDefEq.respectTransparency false
variable {K L : Type} [Field K] [Algebra ℚ K] [Field L] [Algebra ℚ L]
variable {d e s n : ℕ} {a : ℕ→ℕ}
variable (S : FixedField K d) (D : FixedField L e) (into : L→ₐ[ℚ] K)
variable (F : Choice.Table K) (f : List Bool→K) (k : ℕ) (hk : 0<k)
variable (H : (i : Fin (s+1))→Signature L (targetArity s n k a i.val))
variable (hH : ∀i x,into (H i x)=T.signatures (targetArity s n k a) (targetTable s n k F f) i x)

abbrev queryEncoding := RawClosedNetwork.validatedEncoding (s+1) 1 (targetArity s n k a)

def targetTables : ExactSignatureTables e (s+1) 1 (targetArity s n k a) where
  vertex i x:=D.decode.symm (H i x)
  edge _ u v:=D.decode.symm (Signature.disequality u v)

theorem target_value (q : ExactSignatureTables.Input (s+1) 1 (targetArity s n k a)) :
    (targetTables D k H).evaluate D q=
      (q.val.realize q.property H (fun _=>Signature.disequality)).denote Fin.elim0 := by
  rw [ExactSignatureTables.evaluate_eq_decoded]
  simp only [targetTables,LinearEquiv.apply_symm_apply]

include hH in
theorem mapped_value (q : ExactSignatureTables.Input (s+1) 1 (targetArity s n k a)) :
    into ((targetTables D k H).evaluate D q)=
      Choice.evaluate (targetTable s n k F f) q.val.edges.length q.val.vertices := by
  rw [target_value]
  change into.toRingHom ((q.val.realize q.property H (fun _=>Signature.disequality)).denote Fin.elim0)=_
  rw [←Network.denote_map into.toRingHom]
  have he : (q.val.realize q.property H (fun _=>Signature.disequality)).map into.toRingHom=
      q.val.realize q.property (T.signatures (targetArity s n k a) (targetTable s n k F f))
        (fun _=>Signature.disequality) := by
    unfold Network.map RawClosedNetwork.realize
    congr 1
    · funext v x
      exact hH (q.val.signatureLabel q.property v) x
    · funext e u v
      cases u <;> cases v <;> simp [Signature.disequality]
  rw [he,T.denote]

def context (r : P.Input s n a) : K := P.coefficient (s:=s) (n:=n) (a:=a) F f k (P.residue k hk r)

def contextComputes : Computes (P.inputEncoding s n a) S.encoding (context (s:=s) (n:=n) (a:=a) F f k hk) :=
  GeneralEOTensorPowerRemovalPadding.countComputes.andThen
    (R.computes k hk S.encoding (P.coefficient (s:=s) (n:=n) (a:=a) F f k))

def pre (r : P.Input s n a) := ([P.query F f k hk r],context F f k hk r)

def preComputes : Computes (P.inputEncoding s n a)
    (OracleBatch.contextEncoding (queryEncoding (s:=s) (n:=n) (a:=a) k) S.encoding)
    (pre (s:=s) (n:=n) (a:=a) F f k hk) :=
  pairComputes (fixedListComputes (P.inputEncoding s n a) (queryEncoding k)
    (fun r (_ : Unit)=>P.query F f k hk r) (fun _=>P.queryComputes F f k hk) [()])
    (contextComputes S F f k hk)

def post (p : List L×K) : K := into (p.1.getD 0 0)*p.2

def postComputes : Computes (OracleBatch.contextEncoding D.encoding S.encoding) S.encoding (post into) :=
  (pairComputes
    (((Wiring.firstComputes (framedListEncoding D.encoding) S.encoding).andThen
      (getDComputes D.encoding 0 0)).andThen (FieldCodec.computes D S into.toLinearMap))
    (Wiring.secondComputes (framedListEncoding D.encoding) S.encoding)).andThen
      (Concrete.fieldMultiplication S)

include hH in
theorem recovery (r : P.Input s n a) : P.value F f r=
    post into (OracleBatch.answers ((targetTables D k H).evaluate D) (pre F f k hk r)) := by
  change _=into ((targetTables D k H).evaluate D (P.query F f k hk r))*context F f k hk r
  rw [mapped_value D into F f k H hH]
  exact (P.recover F f k hk r).symm

/-- Constructed counting reduction, with no machine, evaluator, or successful
termination premise. k and the complete family are fixed before runtime. -/
def reduction : PolyTimeOracleReduction (P.inputEncoding s n a) S.encoding
    (queryEncoding k) D.encoding (P.value F f) ((targetTables D k H).evaluate D) :=
  OracleBatch.of_eq (preComputes S F f k hk) (postComputes S D into)
    ((targetTables D k H).outputBound D) (P.value F f) (recovery D into F f k hk H hH)

def queryPolynomial : Polynomial ℕ := (P.queryComputes (s:=s) (n:=n) (a:=a) F f k hk).outputBound.bound

def answerPolynomial : Polynomial ℕ :=
  ((targetTables D k H).outputBound D).bound.comp (queryPolynomial (s:=s) (n:=n) (a:=a) F f k hk)

omit [Algebra ℚ K] in
theorem query_length (r : P.Input s n a) :
    ((queryEncoding k).encode (P.query F f k hk r)).length≤
      (queryPolynomial (s:=s) (n:=n) (a:=a) F f k hk).eval ((P.inputEncoding s n a).encode r).length :=
  (P.queryComputes F f k hk).outputBound.length_le r

omit [Algebra ℚ K] in
theorem answer_length (r : P.Input s n a) :
    (D.encoding.encode ((targetTables D k H).evaluate D (P.query F f k hk r))).length≤
      (answerPolynomial D F f k hk H).eval ((P.inputEncoding s n a).encode r).length := by
  apply le_trans (((targetTables D k H).outputBound D).length_le (P.query F f k hk r))
  simpa only [answerPolynomial,Polynomial.eval_comp] using
    natPolynomial_eval_mono ((targetTables D k H).outputBound D).bound (query_length F f k hk r)

theorem run_trace (oracle : List Bool→List Bool)
    (ho : RepresentsOracle (queryEncoding k) D.encoding ((targetTables D k H).evaluate D) oracle)
    (r : P.Input s n a) :
    ∃t≤(reduction S D into F f k hk H hH).time.eval ((P.inputEncoding s n a).encode r).length,
      OracleBatch.RunsTrace (reduction S D into F f k hk H hH).machine oracle
        ((reduction S D into F f k hk H hH).machine.init ((P.inputEncoding s n a).encode r))
        ((reduction S D into F f k hk H hH).machine.output (S.encoding.encode (P.value F f r)))
        t [(queryEncoding k).encode (P.query F f k hk r)] := by
  have h := OracleBatch.of_eq_run_trace (preComputes S F f k hk) (postComputes S D into)
    ((targetTables D k H).outputBound D) (P.value F f) (recovery D into F f k hk H hH) oracle ho r
  simpa only [reduction,pre,List.map_cons,List.map_nil] using h

/-- Exact one-call accounting includes the identically-zero residue branch. -/
theorem exact_calls_and_primitive (oracle : List Bool→List Bool)
    (ho : RepresentsOracle (queryEncoding k) D.encoding ((targetTables D k H).evaluate D) oracle)
    (r : P.Input s n a) :
    ∃t≤(reduction S D into F f k hk H hH).time.eval ((P.inputEncoding s n a).encode r).length,
      UniversalPairReduction.ThreeQuery.queryCount (reduction S D into F f k hk H hH).machine oracle
        ((reduction S D into F f k hk H hH).machine.init ((P.inputEncoding s n a).encode r)) t=1 ∧
      OracleBatch.primitiveCount (reduction S D into F f k hk H hH).machine oracle
        ((reduction S D into F f k hk H hH).machine.init ((P.inputEncoding s n a).encode r)) t≤
        (Polynomial.C (reduction S D into F f k hk H hH).machine.primitiveBudget*
          (reduction S D into F f k hk H hH).time).eval ((P.inputEncoding s n a).encode r).length := by
  obtain ⟨t,ht,htrace⟩ := run_trace S D into F f k hk H hH oracle ho r
  refine ⟨t,ht,?_,?_⟩
  · simpa only [List.length_singleton] using htrace.count
  · have hp := OracleBatch.primitiveCount_le (reduction S D into F f k hk H hH).machine oracle
      ((reduction S D into F f k hk H hH).machine.init ((P.inputEncoding s n a).encode r)) t
    apply hp.trans
    simpa only [Polynomial.eval_mul,Polynomial.eval_C] using
      Nat.mul_le_mul_left (reduction S D into F f k hk H hH).machine.primitiveBudget ht

/-- Every reachable query is the unique literal padded/grouped valid query,
even when inspecting a time beyond the completed run. -/
def controlled : LengthControlledOracleReduction (P.inputEncoding s n a) S.encoding
    (queryEncoding k) D.encoding (P.value F f) ((targetTables D k H).evaluate D) where
  reduction:=reduction S D into F f k hk H hH
  targetOutput:=(targetTables D k H).outputBound D
  queryBound:=queryPolynomial (s:=s) (n:=n) (a:=a) F f k hk
  safeQuery oracle ho r t c hr hq:=by
    obtain ⟨N,_,htrace⟩ := run_trace S D into F f k hk H hH oracle ho r
    have hm := TraceQueryControl.transcript_member htrace t c hr hq
    have he : c.stk (reduction S D into F f k hk H hH).machine.queryStack=
        (queryEncoding k).encode (P.query F f k hk r) := by simpa only [List.mem_singleton] using hm
    refine ⟨P.query F f k hk r,he,?_⟩
    rw [he]
    exact query_length F f k hk r

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOTensorPowerRemovalReduction
