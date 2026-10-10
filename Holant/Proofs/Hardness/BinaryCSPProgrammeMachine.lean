import Holant.Proofs.Hardness.BinaryCSPProgrammeMachineBase
import Holant.Proofs.Algorithms.TraceQueryControl
import Holant.Proofs.CountingMachines.OracleControl.Storage

/-! One actual original-field oracle programme for the cubic annihilator.
The generic difference interpreter isolates the zero-product assignments;
the same programme then subtracts that answer from the computed 2^variables.
Its runtime, answer bytes, query origin and every-prefix fees are proved here. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryCSPProgrammeMachine
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
variable (F : FixedField K d) (a b c : K) (f : Bool→Bool→K)

def keepMachine := LeftMap.machine (Loop.arithmetic F)
def loopTime : Polynomial ℕ := Loop.arithmeticTime F (V.coordinates F a b c f)
  rootBudget initialBudget (stateBound F a b c f)
def loopOutputBound : Polynomial ℕ := stateBound F a b c f+
  loopTime F a b c f*Polynomial.C (Loop.arithmetic F).primitiveBudget
def keepTime : Polynomial ℕ := 2*stateBound F a b c f+loopTime F a b c f+
  2*loopOutputBound F a b c f+6
def keptBound : Polynomial ℕ := stateBound F a b c f+
  keepTime F a b c f*Polynomial.C (keepMachine F).primitiveBudget

def finishComputes : Computes (pairEncoding F.encoding F.encoding) F.encoding
    (fun p : K × K => p.2-p.1) :=
  (Wiring.swapComputes F.encoding F.encoding).andThen (ThreeModeFilter.subtraction F)

def tailMachine := (keepMachine F).compose (finishComputes F).machine
def tailTime : Polynomial ℕ := keepTime F a b c f+2*keptBound F a b c f+2+
  (finishComputes F).time.comp (keptBound F a b c f)
def post := (initializeComputes F).machine.compose (tailMachine F)
def postTime : Polynomial ℕ := (initializeComputes F).time.comp (transcriptBound F a b c f)+
  2*stateBound F a b c f+2+tailTime F a b c f
def machine := OracleBatch.machine (pre F a b c).machine (post F)
def timePolynomial : Polynomial ℕ :=
  (pre F a b c).time+16*((pre F a b c).outputBound.bound+transcriptBound F a b c f+1)+
    postTime F a b c f
def interpolatedValue (r : Raw) : K := total r-Loop.result F (state a b c f r)

def loop_outputs (r : Raw) :
    TM2OutputsInTime (Loop.arithmetic F).computer ((S.encoding F).encode (state a b c f r))
      (some (F.encoding.encode (Loop.result F (state a b c f r))))
      ((loopTime F a b c f).eval (encoding.encode r).length) :=
  Loop.arithmetic_outputs F (V.coordinates F a b c f) rootBudget initialBudget (stateBound F a b c f)
    (.inl 4) (.inl 3) (by simp) (by simp) (encoding.encode r).length (state a b c f r)
    (initial_bounded F a b c f r) (state_length F a b c f r)

def keep_outputs (r : Raw) :
    TM2OutputsInTime (keepMachine F).computer
      ((initializedEncoding F).encode (state a b c f r,total r))
      (some ((pairEncoding F.encoding F.encoding).encode (Loop.result F (state a b c f r),total r)))
      ((keepTime F a b c f).eval (encoding.encode r).length) := by
  let run := loop_outputs F a b c f r
  let ticks := 2*((S.encoding F).encode (state a b c f r)).length+run.steps+
    2*(F.encoding.encode (Loop.result F (state a b c f r))).length+6
  refine {steps:=ticks,evals_in_steps:=?_,steps_le_m:=?_}
  · exact LeftMap.exact_run (Loop.arithmetic F) _ _ _ run.steps run.evals_in_steps
  dsimp only [ticks]
  have hi := state_length F a b c f r
  have ht := run.steps_le_m
  have ho := (Loop.arithmetic F).output_length_le _ _ _ run
  have hm := Nat.mul_le_mul_right (Loop.arithmetic F).primitiveBudget (le_refl
    ((loopTime F a b c f).eval (encoding.encode r).length))
  simp only [keepTime,loopOutputBound,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_ofNat,Polynomial.eval_C]
  omega

theorem kept_length (r : Raw) :
    ((pairEncoding F.encoding F.encoding).encode (Loop.result F (state a b c f r),total r)).length≤
      (keptBound F a b c f).eval (encoding.encode r).length := by
  have h := (keepMachine F).output_length_le _ _ _ (keep_outputs F a b c f r)
  have hi := initialized_length F a b c f r
  simp only [keptBound,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C]
  omega

def tail_outputs (r : Raw) :
    TM2OutputsInTime (tailMachine F).computer
      ((initializedEncoding F).encode (state a b c f r,total r))
      (some (F.encoding.encode (interpolatedValue F a b c f r)))
      ((tailTime F a b c f).eval (encoding.encode r).length) := by
  let first := keep_outputs F a b c f r
  let last := (finishComputes F).outputs (Loop.result F (state a b c f r),total r)
  let run := Machine.compose_correct (keepMachine F) (finishComputes F).machine _ _ _ _ _ first last
  refine {steps:=run.steps,evals_in_steps:=run.evals_in_steps,steps_le_m:=?_}
  have ht := run.steps_le_m
  have hl := kept_length F a b c f r
  have hf := natPolynomial_eval_mono (finishComputes F).time hl
  simp only [tailTime,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_comp]
  omega

def post_outputs (r : Raw) :
    TM2OutputsInTime (post F).computer ((answerEncoding F).encode (answered a b c f r))
      (some (F.encoding.encode (interpolatedValue F a b c f r)))
      ((postTime F a b c f).eval (encoding.encode r).length) := by
  let first := (initializeComputes F).outputs (answered a b c f r)
  let last := tail_outputs F a b c f r
  let run := Machine.compose_correct (initializeComputes F).machine (tailMachine F) _ _ _ _ _ first last
  refine {steps:=run.steps,evals_in_steps:=run.evals_in_steps,steps_le_m:=?_}
  have ht := run.steps_le_m
  have hi := initialized_length F a b c f r
  have hf := natPolynomial_eval_mono (initializeComputes F).time (answered_length F a b c f r)
  change ((initializedEncoding F).encode
    ((((answered a b c f r).2.1,(answered a b c f r).2.2::(answered a b c f r).1),(0,1)),
      (answered a b c f r).2.2)).length≤_ at hi
  simp only [postTime,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_comp]
  omega

theorem execution_agree (oracle : List Bool→List Bool) (r : Raw)
    (ho : ∀q∈Q.queries r,oracle (encoding.encode q)=F.encoding.encode (V.value f q)) :
    ∃t≤(timePolynomial F a b c f).eval (encoding.encode r).length,
      OracleBatch.RunsTrace (machine F a b c) oracle ((machine F a b c).init (encoding.encode r))
        ((machine F a b c).output (F.encoding.encode (interpolatedValue F a b c f r))) t
        ((Q.queries r).map encoding.encode) := by
  have hm : ((Q.queries r).map encoding.encode).map oracle=
      ((Q.queries r).map (V.value f)).map F.encoding.encode := by
    simp only [List.map_map]
    exact List.map_congr_left (fun q hq => ho q hq)
  have ha := (pre F a b c).outputs r
  have hb := post_outputs F a b c f r
  have ha' : TM2OutputsInTime (pre F a b c).machine.computer (encoding.encode r)
      (some (OracleBatch.word ((Q.queries r).map encoding.encode) ((contextEncoding F).encode (context a b c r))))
      ((pre F a b c).time.eval (encoding.encode r).length) := by
    simpa only [OracleBatch.context_encode,preprocessing] using ha
  have hb' : TM2OutputsInTime (post F).computer
      (OracleBatch.word (((Q.queries r).map encoding.encode).map oracle)
        ((contextEncoding F).encode (context a b c r)))
      (some (F.encoding.encode (interpolatedValue F a b c f r)))
      ((postTime F a b c f).eval (encoding.encode r).length) := by
    rw [hm]
    simpa only [answerEncoding,OracleBatch.context_encode,answered,answers,List.map_map] using hb
  have run := OracleBatch.run_trace (pre F a b c).machine (post F) oracle _ _ _ _
    ha'.steps hb'.steps ha'.evals_in_steps hb'.evals_in_steps
  refine ⟨_,?_,run⟩
  have ht₁ := ha'.steps_le_m
  have ht₂ := hb'.steps_le_m
  have hp := (pre F a b c).outputBound.length_le r
  have hd := answered_length F a b c f r
  have hh := OracleBatch.overhead_le oracle ((Q.queries r).map encoding.encode)
    ((contextEncoding F).encode (context a b c r))
  rw [OracleBatch.context_encode] at hp
  simp only [preprocessing,Prod.fst,Prod.snd] at hp
  rw [answerEncoding,OracleBatch.context_encode] at hd
  simp only [answered,Prod.fst,Prod.snd,answers] at hd
  have hdq : (OracleBatch.word (((Q.queries r).map encoding.encode).map oracle)
      ((contextEncoding F).encode (context a b c r))).length≤
      (transcriptBound F a b c f).eval (encoding.encode r).length := by simpa only [hm] using hd
  simp only [OracleBatch.overhead] at hh
  simp only [timePolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_one]
  omega

theorem execution (oracle : List Bool→List Bool)
    (ho : RepresentsOracle encoding F.encoding (V.value f) oracle) (r : Raw) :
    ∃t≤(timePolynomial F a b c f).eval (encoding.encode r).length,
      OracleBatch.RunsTrace (machine F a b c) oracle ((machine F a b c).init (encoding.encode r))
        ((machine F a b c).output (F.encoding.encode (interpolatedValue F a b c f r))) t
        ((Q.queries r).map encoding.encode) :=
  execution_agree F a b c f oracle r (fun q _ => ho q)

def reduction : PolyTimeOracleReduction encoding F.encoding encoding F.encoding
    (interpolatedValue F a b c f) (V.value f) where
  machine:=machine F a b c
  time:=timePolynomial F a b c f
  correct oracle ho r:=by
    let h:=execution F a b c f oracle ho r
    exact {steps:=h.choose,steps_le_m:=h.choose_spec.1,evals_in_steps:=h.choose_spec.2.run}

def controlled : LengthControlledOracleReduction encoding F.encoding encoding F.encoding
    (interpolatedValue F a b c f) (V.value f) where
  reduction:=reduction F a b c f
  targetOutput:=V.targetOutput F a b c f
  queryBound:=(pre F a b c).outputBound.bound
  safeQuery oracle ho r t cfg hr hq:=by
    obtain ⟨n,_,ht⟩:=execution F a b c f oracle ho r
    have hm:=Holant.LocalDrafts.MainChain.TraceQueryControl.transcript_member ht t cfg hr hq
    obtain ⟨q,hmem,he⟩:=List.mem_map.mp hm
    exact ⟨q,he.symm,(OracleBatch.member_length_le _ _ hm).trans
      (OracleBatch.query_context_length_le (pre F a b c) r).1⟩

theorem every_prefix_fees (oracle : List Bool→List Bool)
    (ho : RepresentsOracle encoding F.encoding (V.value f) oracle) (r : Raw) (t : ℕ)
    (ht : t≤(timePolynomial F a b c f).eval (encoding.encode r).length) :
    Holant.LocalDrafts.RemoteWork.CountingBridge.OracleControl.runFee
      (machine F a b c) oracle (encoding.encode r) t≤
      (Holant.LocalDrafts.RemoteWork.CountingBridge.OracleControl.feePolynomial
        (controlled F a b c f)).eval (encoding.encode r).length :=
  Holant.LocalDrafts.RemoteWork.CountingBridge.OracleControl.runFee_le
    (controlled F a b c f) oracle ho r t ht

theorem every_prefix_storage (oracle : List Bool→List Bool)
    (ho : RepresentsOracle encoding F.encoding (V.value f) oracle) (r : Raw) (t : ℕ)
    (ht : t≤(timePolynomial F a b c f).eval (encoding.encode r).length)
    (cfg : (machine F a b c).Cfg)
    (hr : (machine F a b c).run oracle (encoding.encode r) t=some cfg) :
    (Holant.LocalDrafts.RemoteWork.CountingBridge.OracleControl.configurationWord (machine F a b c) cfg).length≤
      (Holant.LocalDrafts.RemoteWork.CountingBridge.OracleControl.codedStoragePolynomial
        (controlled F a b c f)).eval (encoding.encode r).length :=
  Holant.LocalDrafts.RemoteWork.CountingBridge.OracleControl.coded_storage_le
    (controlled F a b c f) oracle ho r t ht cfg hr

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryCSPProgrammeMachine
