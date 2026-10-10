import Holant.Proofs.Hardness.ThreeModeMachineBase
import Holant.Proofs.Hardness.ThreeModeProgrammeRootBounds
import Holant.Proofs.Hardness.ThreeModeFilterExecution

/-! End-to-end actual oracle programme for the original three-mode chain
queries. All preprocessing, the adjacent-difference passes, accumulated
denominator and division are executed by one fixed finite machine. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.ThreeModeMachine
open Turing Computability Holant Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines FixedGadgetSubstitution
open Holant.OneHot
namespace Loop
export ThreeModeFilterLoop (arithmetic arithmeticTime arithmetic_outputs result)
end Loop
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false
variable {K : Type} [Field K] [Algebra ℚ K] {n : ℕ}
variable {F : FixedField K n} {T : ExactSignatureTables n 1 1 Q.arity} (d : Data F T)

def post := (initializeComputes (F:=F)).machine.compose (Loop.arithmetic F)
def machine := OracleBatch.machine (pre d).machine (post (F:=F))
def interpolatedValue (r : Q.Input) : K := Loop.result F (state d r)

def postTime : Polynomial ℕ := (initializeComputes (F:=F)).time.comp (transcriptBound d)+
  2*stateBound d+2+Loop.arithmeticTime F (coordinates d) rootBudget initialBudget (stateBound d)

def timePolynomial : Polynomial ℕ :=
  (pre d).time+16*((pre d).outputBound.bound+transcriptBound d+1)+postTime d

theorem initial_bounded (r : Q.Input) :
    Filter.Bounded (base d) (rootBudget.eval (Q.sourceEncoding.encode r).length)
      (initialBudget.eval (Q.sourceEncoding.encode r).length) (state d r) := by
  have hm : Q.count r≤(Q.sourceEncoding.encode r).length := occurrences_le_input_length 1 r.val
  have hl : ArithmeticSize.Bound (base d) 1 d.lam := literal_bound d 0
  have hu : ArithmeticSize.Bound (base d) 1 d.mu := literal_bound d 1
  have hv : ArithmeticSize.Bound (base d) 1 d.nu := literal_bound d 2
  have hr := ThreeModeProgrammeRootBounds.roots_bound (base d) hl hu hv (Q.count r)
  have hw := ThreeModeProgrammeRootBounds.desired_bound (base d) hl (Q.count r)
  refine ⟨?_,?_,?_,?_⟩
  · intro x hx
    exact (hr x hx).mono (.inl 4) (base_unit d) (by simp [rootBudget];omega)
  · intro y hy
    exact (answer_bound d r y hy).mono (.inl 4) (base_unit d) (by simp [initialBudget])
  · exact hw.mono (.inl 4) (base_unit d) (by simp [rootBudget];omega)
  · exact hw.mono (.inl 4) (base_unit d) (by simp [initialBudget,rootBudget];omega)

def post_outputs (r : Q.Input) :
    TM2OutputsInTime (post (F:=F)).computer ((answerEncoding (F:=F)).encode (answered d r))
      (some (F.encoding.encode (interpolatedValue d r)))
      ((postTime d).eval (Q.sourceEncoding.encode r).length) := by
  let first := (initializeComputes (F:=F)).outputs (answered d r)
  let last := Loop.arithmetic_outputs F (coordinates d) rootBudget initialBudget (stateBound d)
    (.inl 4) (.inl 3) (base_unit d) (base_minus d)
    (Q.sourceEncoding.encode r).length (state d r) (initial_bounded d r) (state_length d r)
  let all := Machine.compose_correct (initializeComputes (F:=F)).machine (Loop.arithmetic F) _ _ _ _ _ first last
  refine {steps:=all.steps,evals_in_steps:=all.evals_in_steps,steps_le_m:=?_}
  have ht := all.steps_le_m
  have hf := natPolynomial_eval_mono (initializeComputes (F:=F)).time (answered_length d r)
  have hs := state_length d r
  change ((Filter.encoding F).encode (((answered d r).2.1,(answered d r).1),
    ((answered d r).2.2,(answered d r).2.2))).length≤_ at hs
  simp only [postTime,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_comp]
  omega

/-- Exact ordered query transcript; pre/post machines make no oracle calls. -/
theorem execution (oracle : List Bool→List Bool)
    (ho : RepresentsOracle Q.targetEncoding F.encoding (T.evaluate F) oracle) (r : Q.Input) :
    ∃t≤(timePolynomial d).eval (Q.sourceEncoding.encode r).length,
      OracleBatch.RunsTrace (machine d) oracle ((machine d).init (Q.sourceEncoding.encode r))
        ((machine d).output (F.encoding.encode (interpolatedValue d r))) t
        ((Q.queries r).map Q.targetEncoding.encode) := by
  have hm := OracleBatch.oracle_encoded_list oracle ho (Q.queries r)
  have ha := (pre d).outputs r
  have hb := post_outputs d r
  rw [←answered_eq,OracleBatch.context_encode] at hb
  have hb' : TM2OutputsInTime (post (F:=F)).computer
      (OracleBatch.word (((Q.queries r).map Q.targetEncoding.encode).map oracle)
        ((contextEncoding (F:=F)).encode (context d r)))
      (some (F.encoding.encode (interpolatedValue d r)))
      ((postTime d).eval (Q.sourceEncoding.encode r).length) := by
    simp only [OracleBatch.answers] at hb
    rw [hm]
    exact hb
  have ha' : TM2OutputsInTime (pre d).machine.computer (Q.sourceEncoding.encode r)
      (some (OracleBatch.word ((Q.queries r).map Q.targetEncoding.encode)
        ((contextEncoding (F:=F)).encode (context d r))))
      ((pre d).time.eval (Q.sourceEncoding.encode r).length) := by
    simp only [OracleBatch.context_encode] at ha
    exact ha
  have run := OracleBatch.run_trace (pre d).machine (post (F:=F)) oracle _ _ _ _
    ha'.steps hb'.steps ha'.evals_in_steps hb'.evals_in_steps
  refine ⟨_,?_,run⟩
  have ht₁ := ha'.steps_le_m
  have ht₂ := hb'.steps_le_m
  have hp := (pre d).outputBound.length_le r
  have hd := answered_length d r
  have hh := OracleBatch.overhead_le oracle ((Q.queries r).map Q.targetEncoding.encode)
    ((contextEncoding (F:=F)).encode (context d r))
  rw [OracleBatch.context_encode] at hp
  rw [←answered_eq,OracleBatch.context_encode] at hd
  simp only [OracleBatch.answers,preprocessing,Prod.fst,Prod.snd] at hd
  simp only [preprocessing,Prod.fst,Prod.snd] at hp
  have hdq : (OracleBatch.word (((Q.queries r).map Q.targetEncoding.encode).map oracle)
      ((contextEncoding (F:=F)).encode (context d r))).length≤
      (transcriptBound d).eval (Q.sourceEncoding.encode r).length := by
    simpa only [hm] using hd
  simp only [OracleBatch.overhead] at hh
  simp only [timePolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_one]
  omega

def reduction : PolyTimeOracleReduction Q.sourceEncoding F.encoding
    Q.targetEncoding F.encoding (interpolatedValue d) (T.evaluate F) where
  machine := machine d
  time := timePolynomial d
  correct oracle ho r := by
    let hr := execution d oracle ho r
    exact {steps:=hr.choose,steps_le_m:=hr.choose_spec.1,evals_in_steps:=hr.choose_spec.2.run}

theorem exact_calls_and_primitive (oracle : List Bool→List Bool)
    (ho : RepresentsOracle Q.targetEncoding F.encoding (T.evaluate F) oracle) (r : Q.Input) :
    ∃t≤(timePolynomial d).eval (Q.sourceEncoding.encode r).length,
      UniversalPairReduction.ThreeQuery.queryCount (machine d) oracle
        ((machine d).init (Q.sourceEncoding.encode r)) t=Q.sampleCount r ∧
      OracleBatch.primitiveCount (machine d) oracle ((machine d).init (Q.sourceEncoding.encode r)) t≤
        (Polynomial.C (machine d).primitiveBudget*timePolynomial d).eval (Q.sourceEncoding.encode r).length := by
  obtain ⟨t,ht,hr⟩ := execution d oracle ho r
  refine ⟨t,ht,?_,?_⟩
  · simpa only [List.length_map,Q.query_count] using hr.count
  · exact (OracleBatch.primitiveCount_le _ _ _ _).trans (by
      simpa only [Polynomial.eval_mul,Polynomial.eval_C] using Nat.mul_le_mul_left (machine d).primitiveBudget ht)

/-- The finite field machine's value is the intended annihilator quotient. -/
theorem value_formula (r : Q.Input) :
    interpolatedValue d r = A.differenceFilter
      (Roots.roots d.lam d.mu d.nu (Q.count r)) (values d r) 0 /
        A.denominator (Q.count r) d.lam d.mu d.nu := by
  have hround : (A.rootIndices (Q.count r)).length≤((Filter.encoding F).encode (state d r)).length := by
    have h := ThreeModeFilter.list_counts_le_bytes F (state d r)
    simpa only [state,Roots.roots,List.length_map] using h.1
  unfold interpolatedValue Loop.result ThreeModeFilterLoop.value
  rw [state_eq_initial]
  exact ThreeModeAnnihilatorFilterExtraction.finalValue_eq _ _ _ _ _ _ (by
    simpa only [←state_eq_initial d r] using hround)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.ThreeModeMachine
