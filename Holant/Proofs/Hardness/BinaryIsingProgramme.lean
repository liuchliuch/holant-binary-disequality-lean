import Holant.Proofs.Hardness.BinaryIsingProgrammeBase
import Holant.Proofs.Algorithms.TraceQueryControl
import Holant.Proofs.CountingMachines.OracleControl.Storage

/-! A completed finite Boolean-stack oracle programme, with actual root
traversal, field operations, positive query transcript, final division by two,
answer bytes, primitive fees, and every-prefix storage bounds. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryIsingProgramme
open Turing Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open Holant.OneHot BinaryCSPProgrammeCore
namespace Loop
export ThreeModeFilterLoop (arithmetic arithmeticTime arithmetic_outputs result)
end Loop
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false
variable {K : Type} [Field K] [Algebra ℚ K] {d : ℕ}
variable (F : FixedField K d) (p q : K)

def halfComputes : Computes F.encoding F.encoding (fun x : K=>x/2) :=
  congrComputes ((pairComputes (identityComputes F.encoding)
    (constantComputes F.encoding F.encoding (2 : K)⁻¹)).andThen (Concrete.fieldMultiplication F))
    (fun _=>by simp [div_eq_mul_inv])

def loopTime : Polynomial ℕ := Loop.arithmeticTime F (Q.coordinates F p q)
  rootBudget initialBudget (stateBound F p q)
def loopOutputBound : Polynomial ℕ := stateBound F p q+
  loopTime F p q*Polynomial.C (Loop.arithmetic F).primitiveBudget
def tailMachine := (Loop.arithmetic F).compose (halfComputes F).machine
def tailTime : Polynomial ℕ := loopTime F p q+2*loopOutputBound F p q+2+
  (halfComputes F).time.comp (loopOutputBound F p q)
def post := (initializeComputes F).machine.compose (tailMachine F)
def postTime : Polynomial ℕ := (initializeComputes F).time.comp (transcriptBound F p q)+
  2*stateBound F p q+2+tailTime F p q
def machine := OracleBatch.machine (pre F p q).machine (post F)
def timePolynomial : Polynomial ℕ :=
  (pre F p q).time+16*((pre F p q).outputBound.bound+transcriptBound F p q+1)+postTime F p q
def interpolatedValue (r : Raw) : K := Loop.result F (state p q r)/2

def loop_outputs (r : Raw) :
    TM2OutputsInTime (Loop.arithmetic F).computer ((S.encoding F).encode (state p q r))
      (some (F.encoding.encode (Loop.result F (state p q r))))
      ((loopTime F p q).eval (encoding.encode r).length) :=
  Loop.arithmetic_outputs F (Q.coordinates F p q) rootBudget initialBudget (stateBound F p q)
    (.inl 4) (.inl 5) (by simp) (by simp) (encoding.encode r).length (state p q r)
    (initial_bounded F p q r) (state_length F p q r)

theorem loop_output_length (r : Raw) :
    (F.encoding.encode (Loop.result F (state p q r))).length≤
      (loopOutputBound F p q).eval (encoding.encode r).length := by
  have ho := (Loop.arithmetic F).output_length_le _ _ _ (loop_outputs F p q r)
  have hi := state_length F p q r
  simp only [loopOutputBound,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C]
  omega

def tail_outputs (r : Raw) :
    TM2OutputsInTime (tailMachine F).computer ((S.encoding F).encode (state p q r))
      (some (F.encoding.encode (interpolatedValue F p q r)))
      ((tailTime F p q).eval (encoding.encode r).length) := by
  let first := loop_outputs F p q r
  let last := (halfComputes F).outputs (Loop.result F (state p q r))
  let run := Machine.compose_correct (Loop.arithmetic F) (halfComputes F).machine _ _ _ _ _ first last
  refine {steps:=run.steps,evals_in_steps:=run.evals_in_steps,steps_le_m:=?_}
  have ht := run.steps_le_m
  have hl := loop_output_length F p q r
  have hf := natPolynomial_eval_mono (halfComputes F).time hl
  simp only [tailTime,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_comp]
  omega

def post_outputs (r : Raw) :
    TM2OutputsInTime (post F).computer ((answerEncoding F).encode (answered p q r))
      (some (F.encoding.encode (interpolatedValue F p q r)))
      ((postTime F p q).eval (encoding.encode r).length) := by
  let first := (initializeComputes F).outputs (answered p q r)
  let last := tail_outputs F p q r
  let run := Machine.compose_correct (initializeComputes F).machine (tailMachine F) _ _ _ _ _ first last
  refine {steps:=run.steps,evals_in_steps:=run.evals_in_steps,steps_le_m:=?_}
  have ht := run.steps_le_m
  have hi := state_length F p q r
  have hf := natPolynomial_eval_mono (initializeComputes F).time (answered_length F p q r)
  change ((S.encoding F).encode
    (((answered p q r).2.1,(answered p q r).2.2.2::(answered p q r).1),
      ((answered p q r).2.2.1,1))).length≤_ at hi
  simp only [postTime,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_comp]
  omega

theorem execution_agree (oracle : List Bool→List Bool) (r : Raw)
    (ho : ∀a∈queries r,oracle (Q.queryEncoding.encode a)=F.encoding.encode (Q.value p q a)) :
    ∃t≤(timePolynomial F p q).eval (encoding.encode r).length,
      OracleBatch.RunsTrace (machine F p q) oracle ((machine F p q).init (encoding.encode r))
        ((machine F p q).output (F.encoding.encode (interpolatedValue F p q r))) t
        ((queries r).map Q.queryEncoding.encode) := by
  have hm : ((queries r).map Q.queryEncoding.encode).map oracle=
      ((queries r).map (Q.value p q)).map F.encoding.encode := by
    simp only [List.map_map]
    exact List.map_congr_left (fun a ha=>ho a ha)
  have ha := (pre F p q).outputs r
  have hb := post_outputs F p q r
  have ha' : TM2OutputsInTime (pre F p q).machine.computer (encoding.encode r)
      (some (OracleBatch.word ((queries r).map Q.queryEncoding.encode)
        ((contextEncoding F).encode (context p q r))))
      ((pre F p q).time.eval (encoding.encode r).length) := by
    simpa only [OracleBatch.context_encode,preprocessing] using ha
  have hb' : TM2OutputsInTime (post F).computer
      (OracleBatch.word (((queries r).map Q.queryEncoding.encode).map oracle)
        ((contextEncoding F).encode (context p q r)))
      (some (F.encoding.encode (interpolatedValue F p q r)))
      ((postTime F p q).eval (encoding.encode r).length) := by
    rw [hm]
    simpa only [answerEncoding,OracleBatch.context_encode,answered,answers,List.map_map] using hb
  have run := OracleBatch.run_trace (pre F p q).machine (post F) oracle _ _ _ _
    ha'.steps hb'.steps ha'.evals_in_steps hb'.evals_in_steps
  refine ⟨_,?_,run⟩
  have ht₁ := ha'.steps_le_m
  have ht₂ := hb'.steps_le_m
  have hp := (pre F p q).outputBound.length_le r
  have hd := answered_length F p q r
  have hh := OracleBatch.overhead_le oracle ((queries r).map Q.queryEncoding.encode)
    ((contextEncoding F).encode (context p q r))
  rw [OracleBatch.context_encode] at hp
  simp only [preprocessing] at hp
  rw [answerEncoding,OracleBatch.context_encode] at hd
  simp only [answered,answers] at hd
  have hdq : (OracleBatch.word (((queries r).map Q.queryEncoding.encode).map oracle)
      ((contextEncoding F).encode (context p q r))).length≤
      (transcriptBound F p q).eval (encoding.encode r).length := by simpa only [hm] using hd
  simp only [OracleBatch.overhead] at hh
  simp only [timePolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_one]
  omega

theorem execution (oracle : List Bool→List Bool)
    (ho : RepresentsOracle Q.queryEncoding F.encoding (Q.value p q) oracle) (r : Raw) :
    ∃t≤(timePolynomial F p q).eval (encoding.encode r).length,
      OracleBatch.RunsTrace (machine F p q) oracle ((machine F p q).init (encoding.encode r))
        ((machine F p q).output (F.encoding.encode (interpolatedValue F p q r))) t
        ((queries r).map Q.queryEncoding.encode) :=
  execution_agree F p q oracle r (fun a _=>ho a)

def reduction : PolyTimeOracleReduction encoding F.encoding Q.queryEncoding F.encoding
    (interpolatedValue F p q) (Q.value p q) where
  machine:=machine F p q
  time:=timePolynomial F p q
  correct oracle ho r:=by
    let h:=execution F p q oracle ho r
    exact {steps:=h.choose,steps_le_m:=h.choose_spec.1,evals_in_steps:=h.choose_spec.2.run}

def controlled : LengthControlledOracleReduction encoding F.encoding Q.queryEncoding F.encoding
    (interpolatedValue F p q) (Q.value p q) where
  reduction:=reduction F p q
  targetOutput:=Q.targetOutput F p q
  queryBound:=(pre F p q).outputBound.bound
  safeQuery oracle ho r t cfg hr hq:=by
    obtain ⟨n,_,ht⟩:=execution F p q oracle ho r
    have hm:=Holant.LocalDrafts.MainChain.TraceQueryControl.transcript_member ht t cfg hr hq
    obtain ⟨a,hmem,he⟩:=List.mem_map.mp hm
    exact ⟨a,he.symm,(OracleBatch.member_length_le _ _ hm).trans
      (OracleBatch.query_context_length_le (pre F p q) r).1⟩

theorem every_prefix_fees (oracle : List Bool→List Bool)
    (ho : RepresentsOracle Q.queryEncoding F.encoding (Q.value p q) oracle) (r : Raw) (t : ℕ)
    (ht : t≤(timePolynomial F p q).eval (encoding.encode r).length) :
    Holant.LocalDrafts.RemoteWork.CountingBridge.OracleControl.runFee
      (machine F p q) oracle (encoding.encode r) t≤
      (Holant.LocalDrafts.RemoteWork.CountingBridge.OracleControl.feePolynomial
        (controlled F p q)).eval (encoding.encode r).length :=
  Holant.LocalDrafts.RemoteWork.CountingBridge.OracleControl.runFee_le
    (controlled F p q) oracle ho r t ht

theorem every_prefix_storage (oracle : List Bool→List Bool)
    (ho : RepresentsOracle Q.queryEncoding F.encoding (Q.value p q) oracle) (r : Raw) (t : ℕ)
    (ht : t≤(timePolynomial F p q).eval (encoding.encode r).length)
    (cfg : (machine F p q).Cfg)
    (hr : (machine F p q).run oracle (encoding.encode r) t=some cfg) :
    (Holant.LocalDrafts.RemoteWork.CountingBridge.OracleControl.configurationWord (machine F p q) cfg).length≤
      (Holant.LocalDrafts.RemoteWork.CountingBridge.OracleControl.codedStoragePolynomial
        (controlled F p q)).eval (encoding.encode r).length :=
  Holant.LocalDrafts.RemoteWork.CountingBridge.OracleControl.coded_storage_le
    (controlled F p q) oracle ho r t ht cfg hr

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryIsingProgramme
