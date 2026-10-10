import Holant.Proofs.Dichotomy.Closure.Complement.GlobalCloseCompletionComplementQ4BatchTiming

/-! The complete actual oracle programme for spectral recovery. Its query
transcript consists solely of the validated original-dictionary native chains;
all four-loop preprocessing and shrinking-list arithmetic are charged. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4BatchExecution
open Turing Computability Holant Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing FixedGadgetSubstitution
namespace B
export GlobalCloseCompletionComplementQ4Batch
  (Input inputEncoding queryEncoding contextEncoding answerEncoding oldTables queries context preprocessing
   pre post machine answered result queriesComputes)
end B
namespace T
export GlobalCloseCompletionComplementQ4BatchTiming (transcript postTime answered_length post_outputs)
end T
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 900000
set_option Elab.async false
variable {K : Type} [Field K] [Algebra ℚ K] [CharZero K] {degree s : ℕ} {a : ℕ→ℕ}
variable (F : FixedField K degree) (H : (i : Fin s)→Signature K (a i.val))
variable (N : NativeAntiTargetSource.Output H 4) (v : Fin 4→K) (support : Bool) (j : Fin 4)

def timePolynomial : Polynomial ℕ:=(B.pre F H N v support j).time+
  16*((B.pre F H N v support j).outputBound.bound+T.transcript F H N v support j+1)+
  T.postTime F H N v support j

theorem execution (oracle : List Bool→List Bool)
    (ho : RepresentsOracle (B.queryEncoding (s:=s) (a:=a)) F.encoding ((B.oldTables F H).evaluate F) oracle)
    (x : B.Input H N) :
    ∃t≤(timePolynomial F H N v support j).eval ((B.inputEncoding H N).encode x).length,
      OracleBatch.RunsTrace (B.machine F H N v support j) oracle
        ((B.machine F H N v support j).init ((B.inputEncoding H N).encode x))
        ((B.machine F H N v support j).output (F.encoding.encode (B.result F H N v support j x))) t
        ((B.queries H N v support j x).map (B.queryEncoding (s:=s) (a:=a)).encode) := by
  have hm:=OracleBatch.oracle_encoded_list oracle ho (B.queries H N v support j x)
  have ha:=(B.pre F H N v support j).outputs x
  have hb:=T.post_outputs F H N v support j x
  change TM2OutputsInTime (B.post F support).computer
    ((B.answerEncoding F).encode (OracleBatch.answers ((B.oldTables F H).evaluate F) (B.preprocessing H N v support j x)))
      _ _ at hb
  rw [OracleBatch.context_encode] at hb
  have hb' : TM2OutputsInTime (B.post F support).computer
      (OracleBatch.word (((B.queries H N v support j x).map (B.queryEncoding (s:=s) (a:=a)).encode).map oracle)
        ((B.contextEncoding F).encode (B.context H N v support j x)))
      (some (F.encoding.encode (B.result F H N v support j x)))
      ((T.postTime F H N v support j).eval ((B.inputEncoding H N).encode x).length) := by
    rw [hm]
    exact hb
  have ha' : TM2OutputsInTime (B.pre F H N v support j).machine.computer ((B.inputEncoding H N).encode x)
      (some (OracleBatch.word ((B.queries H N v support j x).map (B.queryEncoding (s:=s) (a:=a)).encode)
        ((B.contextEncoding F).encode (B.context H N v support j x))))
      ((B.pre F H N v support j).time.eval ((B.inputEncoding H N).encode x).length) := by
    simpa only [OracleBatch.context_encode,B.preprocessing] using ha
  have run:=OracleBatch.run_trace (B.pre F H N v support j).machine (B.post F support) oracle _ _ _ _
    ha'.steps hb'.steps ha'.evals_in_steps hb'.evals_in_steps
  refine ⟨_,?_,run⟩
  have ht₁:=ha'.steps_le_m
  have ht₂:=hb'.steps_le_m
  have hp:=(B.pre F H N v support j).outputBound.length_le x
  have hd:=T.answered_length F H N v support j x
  have hh:=OracleBatch.overhead_le oracle
    ((B.queries H N v support j x).map (B.queryEncoding (s:=s) (a:=a)).encode)
    ((B.contextEncoding F).encode (B.context H N v support j x))
  rw [OracleBatch.context_encode] at hp
  change (OracleBatch.word ((B.queries H N v support j x).map (B.queryEncoding (s:=s) (a:=a)).encode)
    ((B.contextEncoding F).encode (B.context H N v support j x))).length≤_ at hp
  change ((B.answerEncoding F).encode (OracleBatch.answers ((B.oldTables F H).evaluate F)
    (B.preprocessing H N v support j x))).length≤_ at hd
  rw [OracleBatch.context_encode] at hd
  change (OracleBatch.word (((B.queries H N v support j x).map ((B.oldTables F H).evaluate F)).map F.encoding.encode)
    ((B.contextEncoding F).encode (B.context H N v support j x))).length≤_ at hd
  rw [hm] at hh
  simp only [OracleBatch.overhead] at hh
  simp only [timePolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_one]
  omega

def reduction : PolyTimeOracleReduction (B.inputEncoding H N) F.encoding
    (B.queryEncoding (s:=s) (a:=a)) F.encoding (B.result F H N v support j) ((B.oldTables F H).evaluate F) where
  machine:=B.machine F H N v support j
  time:=timePolynomial F H N v support j
  correct oracle ho x:=by
    let h:=execution F H N v support j oracle ho x
    exact {steps:=h.choose,evals_in_steps:=h.choose_spec.2.run,steps_le_m:=h.choose_spec.1}

def controlled : LengthControlledOracleReduction (B.inputEncoding H N) F.encoding
    (B.queryEncoding (s:=s) (a:=a)) F.encoding (B.result F H N v support j) ((B.oldTables F H).evaluate F) where
  reduction:=reduction F H N v support j
  targetOutput:=(B.oldTables F H).outputBound F
  queryBound:=(B.queriesComputes F H N v support j).outputBound.bound
  safeQuery oracle ho x t cfg run query:=by
    obtain ⟨_,_,trace⟩:=execution F H N v support j oracle ho x
    have member:=Holant.LocalDrafts.MainChain.TraceQueryControl.transcript_member trace t cfg run query
    obtain ⟨q,hq,eqn⟩:=List.mem_map.mp member
    refine ⟨q,eqn.symm,?_⟩
    change (cfg.stk (B.machine F H N v support j).queryStack).length≤_
    rw [eqn.symm]
    have hm:=OracleBatch.member_length_le
      ((B.queries H N v support j x).map (B.queryEncoding (s:=s) (a:=a)).encode)
      ((B.queryEncoding (s:=s) (a:=a)).encode q) (List.mem_map.mpr ⟨q,hq,rfl⟩)
    have hb:=(B.queriesComputes F H N v support j).outputBound.length_le x
    rw [OracleBatch.list_encode] at hb
    exact hm.trans hb

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4BatchExecution
end
