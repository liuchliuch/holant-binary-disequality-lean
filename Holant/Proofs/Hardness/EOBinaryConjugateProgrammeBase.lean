import Holant.Proofs.Hardness.EOBinaryConjugateProgrammeQueries
import Holant.Proofs.Hardness.EOBinaryConjugateProgrammePairs
import Holant.Proofs.Hardness.EOBinaryConjugateProgrammeExecution
import Holant.Proofs.Algorithms.TableFieldTransport
import Holant.Proofs.BinaryInterpolation.OracleAnswerBounds

/-! Honest answered-transcript bounds for the mixed-conjugate programme. The
fixed family contains both four-entry coefficient lists and the actual target
tables. Oracle answers are bounded from emitted query bytes before transport. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryConjugateProgrammeBase
open Turing Computability Holant Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open Holant.OneHot
namespace Q
export EOBinaryConjugateProgrammeQueries (Input inputEncoding count queries queriesComputes originalValue transportAnswers)
end Q
namespace C
export ExactTwoChainQueries (arity TargetInput targetEncoding)
end C
namespace P
export EOBinaryConjugateProgrammePairs (roots computes roots_bound initialComputes)
end P
namespace S
export EOBinaryConjugateProgrammeState (initial State encoding rootsEncoding valuesEncoding)
end S
namespace B
export EOBinaryConjugateProgrammeBounds (Bounded initial_bounded)
end B
namespace T
export RealDenseSignTwistStageAccess (tables evaluate)
end T
namespace Map
export Holant.LocalDrafts.MainChain.TableFieldTransport (mapTables evaluate_map)
end Map
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false
variable {K L : Type} [Field K] [Algebra ℚ K] [Field L] [Algebra ℚ L] [StarRing L]
variable {d e : ℕ} (F : FixedField K d) (G : FixedField L e) (into : K→ₐ[ℚ] L) (f : Signature K 2)

def coefficients : Fin 4→L := fun j=>into (EOBinaryPlaneConjugateQueries.coefficients f j)
abbrev targetTables := T.tables F (EOBinaryPlaneCore.lift f)
abbrev mappedTables := Map.mapTables F G into (targetTables F f)
abbrev Label := Fin 10 ⊕ ExactSignatureTables.CoefficientIndex 1 1 C.arity

def literals : Fin 10→L := ![(coefficients into f) 0,(coefficients into f) 1,
  (coefficients into f) 2,(coefficients into f) 3,star ((coefficients into f) 0),
  star ((coefficients into f) 1),star ((coefficients into f) 2),star ((coefficients into f) 3),1,-1]

def base : Label→L
  | .inl i=>literals into f i
  | .inr i=>G.decode ((mappedTables F G into f).coefficient i)

def coordinates (i : Label) : Fin e→ℚ := G.decode.symm (base F G into f i)
@[simp] theorem decode_coordinates (i : Label) :
    G.decode (coordinates F G into f i)=base F G into f i := by simp [coordinates]
@[simp] theorem base_unit : base F G into f (.inl 8)=1 := rfl
@[simp] theorem base_minus : base F G into f (.inl 9)= -1 := rfl

def targetOutput : PolynomialOutputBound C.targetEncoding F.encoding (Q.originalValue f) where
  bound:=((targetTables F f).outputBound F).bound
  length_le q:=by
    rw [show Q.originalValue f q=(targetTables F f).evaluate F q from (T.evaluate F _ q).symm]
    exact ((targetTables F f).outputBound F).length_le q

theorem mapped_evaluate (q : C.TargetInput) :
    (mappedTables F G into f).evaluate G q=into (Q.originalValue f q) := by
  rw [Map.evaluate_map,T.evaluate]
  rfl

theorem answer_bound (q : C.TargetInput) :
    ArithmeticSize.Bound (base F G into f)
      ((q.val.vertices.length+q.val.edges.length)+q.val.edges.length) (into (Q.originalValue f q)) := by
  rw [←mapped_evaluate F G into f q]
  apply Holant.LocalDrafts.BinaryInterpolation.OracleAnswerBounds.network_bound
    (base F G into f) (.inl 8) (base_unit F G into f)
    (q.val.realize q.property (fun i x=>G.decode ((mappedTables F G into f).vertex i x))
      (fun i a b=>G.decode ((mappedTables F G into f).edge i a b)))
    (fun v x=>.inr (.inl ⟨q.val.signatureLabel q.property v,x⟩))
    (fun edge a b=>.inr (.inr (q.val.edgeLabel q.property edge,a,b)))
    (fun _ _=>rfl) (fun _ _ _=>rfl) Fin.elim0

abbrev contextEncoding := S.rootsEncoding G
abbrev answerEncoding := OracleBatch.contextEncoding F.encoding (contextEncoding G)

def context (r : Q.Input) : List (L×L) := P.roots (coefficients into f) r.val.vertices.length

def contextComputes : Computes Q.inputEncoding (contextEncoding G) (context into f) :=
  (FixedGadgetSubstitution.Compiler.vertexCountComputes 2 1 C.arity).andThen
    (P.computes G (coefficients into f))

def preprocessing (r : Q.Input) := (Q.queries r,context into f r)
def pre : Computes Q.inputEncoding (OracleBatch.contextEncoding C.targetEncoding (contextEncoding G))
    (preprocessing into f) := pairComputes Q.queriesComputes (contextComputes G into f)

def answers (r : Q.Input) : List K := (Q.queries r).map (Q.originalValue f)
def answered (r : Q.Input) : List K×List (L×L) := (answers f r,context into f r)
def state (r : Q.Input) : S.State L := S.initial (context into f r) ((answers f r).map into)

def initializeComputes : Computes (answerEncoding F G) (S.encoding G)
    (fun p : List K×List (L×L)=>S.initial p.2 (p.1.map into)) :=
  (pairComputes (Wiring.secondComputes (framedListEncoding F.encoding) (contextEncoding G))
    ((Wiring.firstComputes (framedListEncoding F.encoding) (contextEncoding G)).andThen
      (Q.transportAnswers F G into))).andThen (P.initialComputes G)

abbrev transcriptBound := OracleBatch.decoderBound (pre G into f) (targetOutput F f)
def stateBound : Polynomial ℕ := (initializeComputes F G into).outputBound.bound.comp (transcriptBound F G into f)
def answerBudget : Polynomial ℕ := 2*Q.queriesComputes.outputBound.bound
def rootBudget : Polynomial ℕ := 4*Polynomial.X

theorem answered_length (r : Q.Input) :
    ((answerEncoding F G).encode (answered into f r)).length≤
      (transcriptBound F G into f).eval (Q.inputEncoding.encode r).length :=
  OracleBatch.decoder_length_le (pre G into f) (targetOutput F f) r

theorem state_length (r : Q.Input) :
    ((S.encoding G).encode (state into f r)).length≤
      (stateBound F G into f).eval (Q.inputEncoding.encode r).length := by
  have h:=(initializeComputes F G into).outputBound.length_le (answered into f r)
  exact h.trans (by
    simpa only [stateBound,Polynomial.eval_comp] using natPolynomial_eval_mono
      (initializeComputes F G into).outputBound.bound (answered_length F G into f r))

theorem emitted_answer_bound (r : Q.Input) (y : L) (hy : y∈(answers f r).map into) :
    ArithmeticSize.Bound (base F G into f) (answerBudget.eval (Q.inputEncoding.encode r).length) y := by
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hy
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp ha
  have hmember := OracleBatch.member_length_le ((Q.queries r).map C.targetEncoding.encode)
    (C.targetEncoding.encode q) (List.mem_map.mpr ⟨q,hq,rfl⟩)
  have hlist := Q.queriesComputes.outputBound.length_le r
  rw [OracleBatch.list_encode] at hlist
  have hsize := q.val.counts_le_encoded_length
  apply (answer_bound F G into f q).mono (.inl 8) (base_unit F G into f)
  simp only [answerBudget,Polynomial.eval_mul,Polynomial.eval_ofNat]
  change q.val.vertices.length+q.val.edges.length≤(C.targetEncoding.encode q).length at hsize
  omega

theorem initial_bounded (r : Q.Input) :
    B.Bounded (fun i=>G.decode (coordinates F G into f i))
      (rootBudget.eval (Q.inputEncoding.encode r).length)
      (answerBudget.eval (Q.inputEncoding.encode r).length) 0 (state into f r) := by
  simp only [decode_coordinates]
  have hsize:=r.val.counts_le_encoded_length
  apply B.initial_bounded (base F G into f) (.inl 8) (base_unit F G into f)
  · have hc (j : Fin 4) : ArithmeticSize.Bound (base F G into f) 1 (coefficients into f j) := by
      fin_cases j
      · exact ArithmeticSize.Bound.coefficient (coeff:=base F G into f) (.inl 0)
      · exact ArithmeticSize.Bound.coefficient (coeff:=base F G into f) (.inl 1)
      · exact ArithmeticSize.Bound.coefficient (coeff:=base F G into f) (.inl 2)
      · exact ArithmeticSize.Bound.coefficient (coeff:=base F G into f) (.inl 3)
    have hs (j : Fin 4) : ArithmeticSize.Bound (base F G into f) 1 (star (coefficients into f j)) := by
      fin_cases j
      · exact ArithmeticSize.Bound.coefficient (coeff:=base F G into f) (.inl 4)
      · exact ArithmeticSize.Bound.coefficient (coeff:=base F G into f) (.inl 5)
      · exact ArithmeticSize.Bound.coefficient (coeff:=base F G into f) (.inl 6)
      · exact ArithmeticSize.Bound.coefficient (coeff:=base F G into f) (.inl 7)
    intro p hp
    have h:=P.roots_bound (coefficients into f) (base F G into f) (.inl 8)
      (base_unit F G into f) hc hs r.val.vertices.length p hp
    have hb : 4*r.val.vertices.length≤rootBudget.eval (Q.inputEncoding.encode r).length := by
      simp only [rootBudget,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]
      change r.val.vertices.length+r.val.edges.length≤(Q.inputEncoding.encode r).length at hsize
      omega
    exact ⟨h.1.mono (.inl 8) (base_unit F G into f) hb,h.2.mono (.inl 8) (base_unit F G into f) hb⟩
  · exact emitted_answer_bound F G into f r

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryConjugateProgrammeBase
