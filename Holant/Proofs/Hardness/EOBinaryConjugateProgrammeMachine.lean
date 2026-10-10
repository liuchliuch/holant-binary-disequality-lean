import Holant.Proofs.Hardness.EOBinaryConjugateProgrammeBase
import Holant.Proofs.Algorithms.TraceQueryControl
import Holant.Proofs.CountingMachines.OracleControl.Storage

/-! One actual mixed-conjugate oracle programme, with original-K queries and
answers and common-L arithmetic. The machine, execution, clock, query origins,
answer bytes and every-prefix resource bounds are all constructed internally. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryConjugateProgrammeMachine
open Turing Computability Holant Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open EOBinaryConjugateProgrammeBase
namespace Loop
export EOBinaryConjugateProgrammeLoop (arithmetic arithmeticTime arithmetic_outputs result)
end Loop
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false
variable {K L : Type} [Field K] [Algebra ℚ K] [Field L] [Algebra ℚ L] [StarRing L]
variable {d e : ℕ} (F : FixedField K d) (G : FixedField L e) (into : K→ₐ[ℚ] L) (f : Signature K 2)

def loopTime : Polynomial ℕ := Loop.arithmeticTime G (coordinates F G into f)
  rootBudget answerBudget 0 (stateBound F G into f)
def post := (initializeComputes F G into).machine.compose (Loop.arithmetic G)
def postTime : Polynomial ℕ := (initializeComputes F G into).time.comp (transcriptBound F G into f)+
  2*stateBound F G into f+2+loopTime F G into f
def machine := OracleBatch.machine (pre G into f).machine (post F G into)
def timePolynomial : Polynomial ℕ :=
  (pre G into f).time+16*((pre G into f).outputBound.bound+transcriptBound F G into f+1)+postTime F G into f
def interpolatedValue (r : Q.Input) : L := Loop.result G (state into f r)

def loop_outputs (r : Q.Input) :
    TM2OutputsInTime (Loop.arithmetic G).computer ((S.encoding G).encode (state into f r))
      (some (G.encoding.encode (interpolatedValue G into f r)))
      ((loopTime F G into f).eval (Q.inputEncoding.encode r).length) :=
  Loop.arithmetic_outputs G (coordinates F G into f) rootBudget answerBudget 0 (stateBound F G into f)
    (.inl 8) (.inl 9) (by simp) (by simp) (Q.inputEncoding.encode r).length (state into f r)
    (by simpa using initial_bounded F G into f r) (state_length F G into f r)

def post_outputs (r : Q.Input) :
    TM2OutputsInTime (post F G into).computer ((answerEncoding F G).encode (answered into f r))
      (some (G.encoding.encode (interpolatedValue G into f r)))
      ((postTime F G into f).eval (Q.inputEncoding.encode r).length) := by
  let first:=(initializeComputes F G into).outputs (answered into f r)
  let last:=loop_outputs F G into f r
  let run:=Machine.compose_correct (initializeComputes F G into).machine (Loop.arithmetic G) _ _ _ _ _ first last
  refine {steps:=run.steps,evals_in_steps:=run.evals_in_steps,steps_le_m:=?_}
  have ht:=run.steps_le_m
  have hs:=state_length F G into f r
  change ((S.encoding G).encode (S.initial (answered into f r).2
    ((answered into f r).1.map into))).length≤_ at hs
  have hf:=natPolynomial_eval_mono (initializeComputes F G into).time (answered_length F G into f r)
  simp only [postTime,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_comp]
  omega

theorem execution_agree (oracle : List Bool→List Bool) (r : Q.Input)
    (ho : ∀q∈Q.queries r,oracle (C.targetEncoding.encode q)=F.encoding.encode (Q.originalValue f q)) :
    ∃t≤(timePolynomial F G into f).eval (Q.inputEncoding.encode r).length,
      OracleBatch.RunsTrace (machine F G into f) oracle
        ((machine F G into f).init (Q.inputEncoding.encode r))
        ((machine F G into f).output (G.encoding.encode (interpolatedValue G into f r))) t
        ((Q.queries r).map C.targetEncoding.encode) := by
  have hm : ((Q.queries r).map C.targetEncoding.encode).map oracle=
      ((Q.queries r).map (Q.originalValue f)).map F.encoding.encode := by
    simp only [List.map_map]
    exact List.map_congr_left (fun q hq=>ho q hq)
  have ha:=(pre G into f).outputs r
  have hb:=post_outputs F G into f r
  have ha' : TM2OutputsInTime (pre G into f).machine.computer (Q.inputEncoding.encode r)
      (some (OracleBatch.word ((Q.queries r).map C.targetEncoding.encode)
        ((contextEncoding G).encode (context into f r))))
      ((pre G into f).time.eval (Q.inputEncoding.encode r).length) := by
    simpa only [OracleBatch.context_encode,preprocessing] using ha
  have hb' : TM2OutputsInTime (post F G into).computer
      (OracleBatch.word (((Q.queries r).map C.targetEncoding.encode).map oracle)
        ((contextEncoding G).encode (context into f r)))
      (some (G.encoding.encode (interpolatedValue G into f r)))
      ((postTime F G into f).eval (Q.inputEncoding.encode r).length) := by
    rw [hm]
    simpa only [answerEncoding,OracleBatch.context_encode,answered,answers,List.map_map] using hb
  have run:=OracleBatch.run_trace (pre G into f).machine (post F G into) oracle _ _ _ _
    ha'.steps hb'.steps ha'.evals_in_steps hb'.evals_in_steps
  refine ⟨_,?_,run⟩
  have ht₁:=ha'.steps_le_m
  have ht₂:=hb'.steps_le_m
  have hp:=(pre G into f).outputBound.length_le r
  have hd:=answered_length F G into f r
  have hh:=OracleBatch.overhead_le oracle ((Q.queries r).map C.targetEncoding.encode)
    ((contextEncoding G).encode (context into f r))
  rw [OracleBatch.context_encode] at hp
  simp only [preprocessing,Prod.fst,Prod.snd] at hp
  rw [answerEncoding,OracleBatch.context_encode] at hd
  simp only [answered,Prod.fst,Prod.snd,answers] at hd
  have hdq : (OracleBatch.word (((Q.queries r).map C.targetEncoding.encode).map oracle)
      ((contextEncoding G).encode (context into f r))).length≤
      (transcriptBound F G into f).eval (Q.inputEncoding.encode r).length := by simpa only [hm] using hd
  simp only [OracleBatch.overhead] at hh
  simp only [timePolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_one]
  omega

theorem execution (oracle : List Bool→List Bool)
    (ho : RepresentsOracle C.targetEncoding F.encoding (Q.originalValue f) oracle) (r : Q.Input) :
    ∃t≤(timePolynomial F G into f).eval (Q.inputEncoding.encode r).length,
      OracleBatch.RunsTrace (machine F G into f) oracle
        ((machine F G into f).init (Q.inputEncoding.encode r))
        ((machine F G into f).output (G.encoding.encode (interpolatedValue G into f r))) t
        ((Q.queries r).map C.targetEncoding.encode) :=
  execution_agree F G into f oracle r (fun q _=>ho q)

def reduction : PolyTimeOracleReduction Q.inputEncoding G.encoding C.targetEncoding F.encoding
    (interpolatedValue G into f) (Q.originalValue f) where
  machine:=machine F G into f
  time:=timePolynomial F G into f
  correct oracle ho r:=by
    let h:=execution F G into f oracle ho r
    exact {steps:=h.choose,steps_le_m:=h.choose_spec.1,evals_in_steps:=h.choose_spec.2.run}

def controlled : LengthControlledOracleReduction Q.inputEncoding G.encoding C.targetEncoding F.encoding
    (interpolatedValue G into f) (Q.originalValue f) where
  reduction:=reduction F G into f
  targetOutput:=targetOutput F f
  queryBound:=(pre G into f).outputBound.bound
  safeQuery oracle ho r t cfg hr hq:=by
    obtain ⟨n,_,ht⟩:=execution F G into f oracle ho r
    have hm:=Holant.LocalDrafts.MainChain.TraceQueryControl.transcript_member ht t cfg hr hq
    obtain ⟨q,hmem,he⟩:=List.mem_map.mp hm
    exact ⟨q,he.symm,(OracleBatch.member_length_le _ _ hm).trans
      (OracleBatch.query_context_length_le (pre G into f) r).1⟩

theorem query_origin (oracle : List Bool→List Bool)
    (ho : RepresentsOracle C.targetEncoding F.encoding (Q.originalValue f) oracle)
    (r : Q.Input) (t : ℕ) (cfg : (machine F G into f).Cfg)
    (hr : (machine F G into f).run oracle (Q.inputEncoding.encode r) t=some cfg)
    (hq : (machine F G into f).IsQuery cfg) :
    ∃k<Q.count r,cfg.stk (machine F G into f).queryStack=
      C.targetEncoding.encode (ExactTwoChainQueries.value (k,r)) := by
  obtain ⟨n,_,ht⟩:=execution F G into f oracle ho r
  have hm:=Holant.LocalDrafts.MainChain.TraceQueryControl.transcript_member ht t cfg hr hq
  obtain ⟨q,hmem,he⟩:=List.mem_map.mp hm
  obtain ⟨k,hk,hq⟩:=EOBinaryConjugateProgrammeQueries.query_origin r q hmem
  exact ⟨k,hk,by rw [he.symm,hq]⟩

theorem every_prefix_fees (oracle : List Bool→List Bool)
    (ho : RepresentsOracle C.targetEncoding F.encoding (Q.originalValue f) oracle) (r : Q.Input) (t : ℕ)
    (ht : t≤(timePolynomial F G into f).eval (Q.inputEncoding.encode r).length) :
    Holant.LocalDrafts.RemoteWork.CountingBridge.OracleControl.runFee
      (machine F G into f) oracle (Q.inputEncoding.encode r) t≤
      (Holant.LocalDrafts.RemoteWork.CountingBridge.OracleControl.feePolynomial
        (controlled F G into f)).eval (Q.inputEncoding.encode r).length :=
  Holant.LocalDrafts.RemoteWork.CountingBridge.OracleControl.runFee_le
    (controlled F G into f) oracle ho r t ht

theorem every_prefix_storage (oracle : List Bool→List Bool)
    (ho : RepresentsOracle C.targetEncoding F.encoding (Q.originalValue f) oracle) (r : Q.Input) (t : ℕ)
    (ht : t≤(timePolynomial F G into f).eval (Q.inputEncoding.encode r).length)
    (cfg : (machine F G into f).Cfg)
    (hr : (machine F G into f).run oracle (Q.inputEncoding.encode r) t=some cfg) :
    (Holant.LocalDrafts.RemoteWork.CountingBridge.OracleControl.configurationWord
      (machine F G into f) cfg).length≤
      (Holant.LocalDrafts.RemoteWork.CountingBridge.OracleControl.codedStoragePolynomial
        (controlled F G into f)).eval (Q.inputEncoding.encode r).length :=
  Holant.LocalDrafts.RemoteWork.CountingBridge.OracleControl.coded_storage_le
    (controlled F G into f) oracle ho r t ht cfg hr

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryConjugateProgrammeMachine
