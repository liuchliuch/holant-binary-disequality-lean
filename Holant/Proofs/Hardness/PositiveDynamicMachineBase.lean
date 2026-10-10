import Holant.Proofs.Hardness.PositiveDynamicQueriesComputes
import Holant.Proofs.Hardness.PositiveDynamicProgrammeRootBounds
import Holant.Proofs.Hardness.ThreeModeAnnihilatorFilterExtraction
import Holant.Proofs.Hardness.ThreeModeFilterBounds
import Holant.Complexity.OracleBatch.ReductionTrace
import Holant.Proofs.BinaryInterpolation.OracleAnswerBounds

/-! Original-byte dynamic query/root preprocessing and literal answer-state wiring
for the actual input-dependent positive-stage filter. The one oracle and one fixed field presentation are
retained throughout, including the final canonical answer word. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.PositiveDynamicMachine
open Turing Computability Holant Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines FixedGadgetSubstitution
open Holant.OneHot
namespace Q
export ExactTwoChainQueries (arity Input TargetInput sourceEncoding targetEncoding)
export PositiveDynamicQueries (count countComputes sampleCount value queries query_count query_count_le)
export PositiveDynamicQueriesComputes (queriesComputes)
end Q
namespace Roots
export PositiveDynamicProgrammeRoots (lam mu nu roots preprocessing preprocessingComputes)
end Roots
namespace Filter
export ThreeModeFilter (State encoding Bounded)
end Filter
namespace A
export ThreeModeAnnihilator (mode rootIndices rootIndices_toFinset rootIndices_length differenceFilter denominator)
end A
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false
variable {K : Type} [Field K] [Algebra ℚ K] {n : ℕ}

structure Data (F : FixedField K n) (T : ExactSignatureTables n 1 1 Q.arity) where
  a : K
  b : K
  c : K
  params : PositiveDynamicParameters.Data

variable {F : FixedField K n} {T : ExactSignatureTables n 1 1 Q.arity} (d : Data F T)

abbrev contextEncoding := pairEncoding (framedListEncoding F.encoding) F.encoding
abbrev answerEncoding := OracleBatch.contextEncoding F.encoding (contextEncoding (F:=F))

def context (r : Q.Input) : List K×K := Roots.preprocessing d.params.constant d.a d.b d.c (Q.count r)

def contextComputes : Computes Q.sourceEncoding (contextEncoding (F:=F)) (context d) :=
  Q.countComputes.andThen (Roots.preprocessingComputes d.params.constant F d.a d.b d.c)

def preprocessing (r : Q.Input) := (Q.queries d.params r,context d r)

def pre : Computes Q.sourceEncoding
    (OracleBatch.contextEncoding Q.targetEncoding (contextEncoding (F:=F))) (preprocessing d) :=
  pairComputes (Q.queriesComputes d.params) (contextComputes d)

def values (r : Q.Input) (k : ℕ) : K := T.evaluate F (Q.value d.params (k,r))

def answerList (r : Q.Input) : List K := (Q.queries d.params r).map (T.evaluate F)

def answered (r : Q.Input) : List K×(List K×K) := (answerList d r,context d r)

@[simp] theorem answered_eq (r : Q.Input) :
    OracleBatch.answers (T.evaluate F) (preprocessing d r)=answered d r := rfl

def state (r : Q.Input) : Filter.State K :=
  ((Roots.roots d.params.constant d.a d.b d.c (Q.count r),answerList d r),
    ((Roots.lam d.params.constant d.a d.b (Q.count r))^(Q.count r),(Roots.lam d.params.constant d.a d.b (Q.count r))^(Q.count r)))

/-- The collected answers and the physically computed root context are wired
into the exact state codec. All duplication and permutation is physical. -/
def initializeComputes : Computes (answerEncoding (F:=F)) (Filter.encoding F)
    (fun z : List K×(List K×K) => ((z.2.1,z.1),(z.2.2,z.2.2))) := by
  let answers := Wiring.firstComputes (framedListEncoding F.encoding) (contextEncoding (F:=F))
  let context := Wiring.secondComputes (framedListEncoding F.encoding) (contextEncoding (F:=F))
  let roots := context.andThen (Wiring.firstComputes (framedListEncoding F.encoding) F.encoding)
  let desired := context.andThen (Wiring.secondComputes (framedListEncoding F.encoding) F.encoding)
  exact pairComputes (pairComputes roots answers) (pairComputes desired desired)

abbrev Index := Fin 6 ⊕ ExactSignatureTables.CoefficientIndex 1 1 Q.arity

def literals : Fin 6→K := PositiveDynamicProgrammeFormulas.coefficients d.a d.b d.c

def coordinates : Index→Fin n→ℚ
  | .inl a => F.decode.symm (literals d a)
  | .inr a => T.coefficient a

def base : Index→K := fun a=>F.decode (coordinates d a)

@[simp] theorem base_literal (i : Fin 6) : base d (.inl i)=literals d i := by
  simp [base,coordinates]

@[simp] theorem base_unit : base d (.inl 5)=1 := by simp [literals,PositiveDynamicProgrammeFormulas.coefficients]
@[simp] theorem base_minus : base d (.inl 3)= -1 := by simp [literals,PositiveDynamicProgrammeFormulas.coefficients]

theorem literal_bound (i : Fin 6) : ArithmeticSize.Bound (base d) 1 (literals d i) := by
  simpa only [base_literal] using (ArithmeticSize.Bound.coefficient (coeff:=base d) (.inl i))

/-- Structural certificate from the actual emitted target graph. -/
theorem target_bound (q : Q.TargetInput) :
    ArithmeticSize.Bound (base d)
      ((q.val.vertices.length+q.val.edges.length)+q.val.edges.length) (T.evaluate F q) := by
  apply Holant.LocalDrafts.BinaryInterpolation.OracleAnswerBounds.network_bound _ (.inl 5) (base_unit d)
    (q.val.realize q.property (fun i x=>F.decode (T.vertex i x))
      (fun i a b=>F.decode (T.edge i a b)))
    (fun v x=>.inr (.inl ⟨q.val.signatureLabel q.property v,x⟩))
    (fun e a b=>.inr (.inr (q.val.edgeLabel q.property e,a,b)))
    (fun _ _=>rfl) (fun _ _ _=>rfl) Fin.elim0

def answerBudget : Polynomial ℕ := 2*(Q.queriesComputes d.params).outputBound.bound

def rootBudget : Polynomial ℕ := PositiveDynamicProgrammeRootBounds.budget d.params.constant

def initialBudget : Polynomial ℕ := answerBudget d+rootBudget d

abbrev transcriptBound := OracleBatch.decoderBound (pre d) (T.outputBound F)

def stateBound : Polynomial ℕ := (initializeComputes (F:=F)).outputBound.bound.comp (transcriptBound d)

theorem answered_length (r : Q.Input) :
    ((answerEncoding (F:=F)).encode (answered d r)).length≤
      (transcriptBound d).eval (Q.sourceEncoding.encode r).length := by
  rw [←answered_eq]
  exact OracleBatch.decoder_length_le (pre d) (T.outputBound F) r

theorem state_length (r : Q.Input) :
    ((Filter.encoding F).encode (state d r)).length≤
      (stateBound d).eval (Q.sourceEncoding.encode r).length := by
  have hs := (initializeComputes (F:=F)).outputBound.length_le (answered d r)
  have hm := natPolynomial_eval_mono (initializeComputes (F:=F)).outputBound.bound (answered_length d r)
  exact hs.trans (by simpa only [stateBound,Polynomial.eval_comp] using hm)

theorem answer_bound (r : Q.Input) (y : K) (hy : y∈answerList d r) :
    ArithmeticSize.Bound (base d) ((answerBudget d).eval (Q.sourceEncoding.encode r).length) y := by
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hy
  have hmember := OracleBatch.member_length_le ((Q.queries d.params r).map Q.targetEncoding.encode)
    (Q.targetEncoding.encode q) (List.mem_map.mpr ⟨q,hq,rfl⟩)
  have hlist := (Q.queriesComputes d.params).outputBound.length_le r
  rw [OracleBatch.list_encode] at hlist
  have hsize := q.val.counts_le_encoded_length
  apply (target_bound d q).mono (.inl 5) (base_unit d)
  simp only [answerBudget,Polynomial.eval_mul,Polynomial.eval_ofNat]
  change q.val.vertices.length+q.val.edges.length≤(Q.targetEncoding.encode q).length at hsize
  omega

/-- Exact list order identifies the real collector with the semantic finite table. -/
theorem state_eq_initial (r : Q.Input) : state d r=
    ThreeModeAnnihilatorFilterExtraction.initial (Q.count r)
      (Roots.lam d.params.constant d.a d.b (Q.count r))
      (Roots.mu d.params.constant d.a d.b d.c (Q.count r))
      (Roots.nu d.params.constant d.a d.b d.c (Q.count r)) (values d r) := by
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · apply List.ext_getElem
      · simp [state,answerList,PositiveDynamicQueries.queries,PositiveDynamicQueries.sampleCount,
          ThreeModeAnnihilatorFilterExtraction.initial,
          ThreeModeAnnihilatorFilterExtraction.spectralRoots,
          ThreeModeAnnihilatorFilterSemantics.table]
      · intro i hi hj
        simp only [state,answerList,PositiveDynamicQueries.queries,
          ThreeModeAnnihilatorFilterExtraction.initial,
          ThreeModeAnnihilatorFilterSemantics.table,values,
          List.getElem_map,List.getElem_range,List.getElem_ofFn]
  · rfl

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.PositiveDynamicMachine
