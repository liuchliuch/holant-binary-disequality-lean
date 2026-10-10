import Holant.Proofs.CountingMachines.StandardMachine.Support.WitnessMachine

set_option backward.isDefEq.respectTransparency false
/-! Locally checked adaptation of the frozen reference proof. Actual two-phase executions. Lists in these statements
describe tapes; all runtime changes use the finite programs in WitnessMachine.
-/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.WitnessMachine
open Turing Computability Holant.Complexity BinaryCompose FixedFieldMachines
open GraphPreprocessing StackProtocol
variable {α : Type} {ea : Encoding α Bool} {f : α → ℕ} (w : SharpPWitness ea f)

@[simp] theorem phaseWords_counter (count input : List Bool) :
    phaseWords w count input (counter w) = count := by
  simp [phaseWords,counter,scratch]
@[simp] theorem phaseWords_scratch (count input : List Bool) :
    phaseWords w count input (scratch w) = input := by simp [phaseWords]

theorem phaseWords_update_counter (count input next : List Bool) :
    Function.update (phaseWords w count input) (counter w) next =
      phaseWords w next input := by
  funext key
  cases key with
  | inl k => by_cases h : k = (preparation w).output <;> simp [phaseWords,counter,scratch,h]
  | inr k => simp [phaseWords,counter,scratch]

theorem phaseWords_update_scratch (count input next : List Bool) :
    Function.update (phaseWords w count input) (scratch w) next =
      phaseWords w count next := by simp only [phaseWords,Function.update_idem]

@[simp] theorem input_lookup (input : List (w.verifier.tm.Γ w.verifier.tm.k₀)) :
    (initList w.verifier.tm input).stk w.verifier.tm.k₀ = input := by simp [initList]

theorem input_update (bit : w.verifier.tm.Γ w.verifier.tm.k₀)
    (input : List (w.verifier.tm.Γ w.verifier.tm.k₀)) :
    Function.update (initList w.verifier.tm input).stk w.verifier.tm.k₀ (bit :: input) =
      (initList w.verifier.tm (bit :: input)).stk := by
  funext key
  by_cases h : key = w.verifier.tm.k₀
  · subst key; simp [initList]
  · simp [initList,h]

theorem scan_pair (log : List Bool) (bit : Bool) (rest scratchWord : List Bool)
    (input : List (w.verifier.tm.Γ w.verifier.tm.k₀)) :
    (machine w).advance (log,phaseCfg w 0 (true :: bit :: rest) scratchWord input) =
      some (log,phaseCfg w 0 rest (bit :: scratchWord) input) := by
  simp [BinaryMachine.advance,BinaryMachine.step,machine,computer,program,phase,
    phaseCfg,initial,Frame.scanStmt,SumStacks.left_stepAux,SumStacks.leftCfg,
    phaseWords_counter,SumStacks.update_left,phaseWords_update_counter,
    phaseWords_update_scratch,TM2.stepAux]

theorem scan_end (log suffix scratchWord : List Bool)
    (input : List (w.verifier.tm.Γ w.verifier.tm.k₀)) :
    (machine w).advance (log,phaseCfg w 0 (false :: suffix) scratchWord input) =
      some (log,phaseCfg w 2 suffix scratchWord input) := by
  simp [BinaryMachine.advance,BinaryMachine.step,machine,computer,program,phase,
    phaseCfg,initial,Frame.scanStmt,SumStacks.left_stepAux,SumStacks.leftCfg,
    phaseWords_counter,SumStacks.update_left,phaseWords_update_counter,TM2.stepAux]

theorem scan_run (word suffix scratchWord log : List Bool)
    (input : List (w.verifier.tm.Γ w.verifier.tm.k₀)) :
    (machine w).run (word.length + 1)
      (log,phaseCfg w 0 (Holant.Algebraic.frame word ++ suffix) scratchWord input) =
      some (log,phaseCfg w 2 suffix (word.reverse ++ scratchWord) input) := by
  induction word generalizing scratchWord with
  | nil => simpa [Holant.Algebraic.frame,BinaryMachine.run] using scan_end w log suffix scratchWord input
  | cons bit word ih =>
    have hf : Holant.Algebraic.frame (bit :: word) =
        true :: bit :: Holant.Algebraic.frame word := rfl
    rw [List.length_cons,hf,List.cons_append,List.cons_append,BinaryMachine.run,
      scan_pair,Option.bind_some]
    simpa only [List.reverse_cons,List.append_assoc,List.singleton_append] using ih (bit :: scratchWord)

theorem check_cons (log count scratchWord : List Bool) (token : Bool)
    (input : List (w.verifier.tm.Γ w.verifier.tm.k₀)) :
    (machine w).advance (log,phaseCfg w 2 (token :: count) scratchWord input) =
      some (log,phaseCfg w 3 count scratchWord input) := by
  simp [BinaryMachine.advance,BinaryMachine.step,machine,computer,program,phase,
    phaseCfg,initial,SumStacks.merge,SumStacks.update_left,phaseWords_counter,
    phaseWords_update_counter,TM2.stepAux]

theorem check_nil (log scratchWord : List Bool)
    (input : List (w.verifier.tm.Γ w.verifier.tm.k₀)) :
    (machine w).advance (log,phaseCfg w 2 [] scratchWord input) =
      some (log,phaseCfg w 4 [] scratchWord input) := by
  simp [BinaryMachine.advance,BinaryMachine.step,machine,computer,program,phase,
    phaseCfg,initial,SumStacks.merge,SumStacks.update_left,phaseWords_counter,
    phaseWords_update_counter,TM2.stepAux]

theorem choice_cons (bit : Bool) (log count scratchWord : List Bool)
    (input : List (w.verifier.tm.Γ w.verifier.tm.k₀)) :
    (machine w).advance (bit :: log,phaseCfg w 3 count scratchWord input) =
      some (log,phaseCfg w 2 count scratchWord
        (w.verifier.inputAlphabet.symm (Sum.inr bit) :: input)) := by
  cases bit <;>
    simp [BinaryMachine.advance,BinaryMachine.step,machine,computer,program,phase,
      phaseCfg,initial,SumStacks.merge,SumStacks.update_right,input_update,TM2.stepAux]

theorem choice_eof (count scratchWord : List Bool)
    (input : List (w.verifier.tm.Γ w.verifier.tm.k₀)) :
    (machine w).advance ([],phaseCfg w 3 count scratchWord input) = none := by
  simp [BinaryMachine.advance,machine,phase,phaseCfg]

/-- The two choices produce different actual configurations even when the
verifier will later ignore that witness bit. They are not duplicate edges. -/
theorem choice_targets_distinct (count scratchWord : List Bool)
    (input : List (w.verifier.tm.Γ w.verifier.tm.k₀)) :
    phaseCfg w 2 count scratchWord (w.verifier.inputAlphabet.symm (Sum.inr false) :: input) ≠
      phaseCfg w 2 count scratchWord (w.verifier.inputAlphabet.symm (Sum.inr true) :: input) := by
  intro h
  have hh := congrArg (fun c : (machine w).Config => (c.stk (.inr w.verifier.tm.k₀)).head?) h
  simp only [phaseCfg,SumStacks.merge,input_lookup,List.head?_cons] at hh
  have hs := Option.some.inj hh
  have hb : false = true := Sum.inr.inj (w.verifier.inputAlphabet.symm.injective hs)
  cases hb

theorem choice_run (bits rest scratchWord : List Bool)
    (input : List (w.verifier.tm.Γ w.verifier.tm.k₀)) :
    (machine w).run (2 * bits.length + 1)
      (bits ++ rest,phaseCfg w 2 (List.replicate bits.length true) scratchWord input) =
      some (rest,phaseCfg w 4 [] scratchWord
        (bits.reverse.map (fun b => w.verifier.inputAlphabet.symm (Sum.inr b)) ++ input)) := by
  induction bits generalizing input with
  | nil => simpa [BinaryMachine.run] using check_nil w rest scratchWord input
  | cons bit bits ih =>
    rw [show 2 * (bit :: bits).length + 1 = (2 * bits.length + 1) + 2 by
      simp only [List.length_cons] <;> omega,BinaryMachine.run_add,BinaryMachine.run_two]
    simp only [List.cons_append,List.length_cons,List.replicate_succ,
      check_cons,choice_cons,Option.bind_some]
    simpa only [List.reverse_cons,List.map_append,List.map_singleton,
      List.append_assoc,List.singleton_append] using
        ih (w.verifier.inputAlphabet.symm (Sum.inr bit) :: input)

theorem choice_short (n : ℕ) (bits scratchWord : List Bool)
    (input : List (w.verifier.tm.Γ w.verifier.tm.k₀)) (h : bits.length < n) :
    (machine w).run (2 * n + 1)
      (bits,phaseCfg w 2 (List.replicate n true) scratchWord input) = none := by
  induction n generalizing bits input with
  | zero => omega
  | succ n ih =>
    rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by omega,
      BinaryMachine.run_add,BinaryMachine.run_two]
    cases bits with
    | nil => simp [List.replicate_succ,check_cons,choice_eof]
    | cons bit bits =>
      simp only [List.replicate_succ,check_cons,choice_cons,Option.bind_some]
      exact ih bits _ (by simpa only [List.length_cons,Nat.succ_lt_succ_iff] using h)

theorem copy_cons (log : List Bool) (bit : Bool) (rest : List Bool)
    (input : List (w.verifier.tm.Γ w.verifier.tm.k₀)) :
    (machine w).advance (log,phaseCfg w 4 [] (bit :: rest) input) =
      some (log,phaseCfg w 4 [] rest
        (w.verifier.inputAlphabet.symm (Sum.inl bit) :: input)) := by
  simp [BinaryMachine.advance,BinaryMachine.step,machine,computer,program,phase,
    phaseCfg,initial,SumStacks.merge,SumStacks.update_left,SumStacks.update_right,
    phaseWords_scratch,phaseWords_update_scratch,input_update,TM2.stepAux]

theorem copy_nil (log : List Bool)
    (input : List (w.verifier.tm.Γ w.verifier.tm.k₀)) :
    (machine w).advance (log,phaseCfg w 4 [] [] input) =
      some (log,phaseCfg w 1 [] [] input) := by
  simp [BinaryMachine.advance,BinaryMachine.step,machine,computer,program,phase,
    phaseCfg,initial,SumStacks.merge,SumStacks.update_left,phaseWords_scratch,
    phaseWords_update_scratch,TM2.stepAux]

theorem copy_run (word log : List Bool)
    (input : List (w.verifier.tm.Γ w.verifier.tm.k₀)) :
    (machine w).run (word.length + 1) (log,phaseCfg w 4 [] word input) =
      some (log,phaseCfg w 1 [] []
        (word.reverse.map (fun b => w.verifier.inputAlphabet.symm (Sum.inl b)) ++ input)) := by
  induction word generalizing input with
  | nil => simpa [BinaryMachine.run] using copy_nil w log input
  | cons bit word ih =>
    rw [List.length_cons,BinaryMachine.run,copy_cons,Option.bind_some]
    simpa only [List.reverse_cons,List.map_append,List.map_singleton,
      List.append_assoc,List.singleton_append] using
        ih (w.verifier.inputAlphabet.symm (Sum.inl bit) :: input)

theorem launch (log : List Bool) (input : List (w.verifier.tm.Γ w.verifier.tm.k₀)) :
    (machine w).advance (log,phaseCfg w 1 [] [] input) =
      some (log,verifierCfg w (initList w.verifier.tm input)) := by
  simp [BinaryMachine.advance,BinaryMachine.step,machine,computer,program,phase,
    phaseCfg,initial,verifierCfg,verifierStates,verifierLabel,SumStacks.rightCfg,
    phaseWords,counter,scratch,initList,TM2.stepAux]

theorem preparation_run_lift (t : ℕ) (log : List Bool) (c d : (preparation w).Config)
    (h : (fun p => p.bind (preparation w).computer.step)^[t] (some c) = some d) :
    (machine w).run t (log,preparationCfg w c) = some (log,preparationCfg w d) := by
  induction t generalizing c with
  | zero => have hd : c = d := Option.some.inj h; subst d; rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply] at h
    cases hs : (preparation w).computer.step c with
    | none =>
      have hn : (fun p => p.bind (preparation w).computer.step)^[t] none = none :=
        Function.iterate_fixed rfl t
      rw [Option.bind_some, hs] at h
      have hf : none = some d := hn.symm.trans h
      cases hf
    | some next =>
      rw [BinaryMachine.run,preparation_step w log c next hs,Option.bind_some]
      exact ih next (by simpa only [Option.bind_some,hs] using h)

theorem preparation_halt (word : List Bool) :
    preparationCfg w (haltList (preparation w).computer word) = phaseCfg w 0 word [] [] := by
  rw [Machine.halt_eq]
  simp only [preparationCfg,embedCfg,preparationStates,preparationLayout,
    SumStacks.leftCfg,phaseCfg,initial,phaseWords,counter,scratch,SumStacks.merge]
  congr 1
  funext key
  cases key with
  | inl key =>
    cases key with
    | inl k => by_cases h : k = (preparation w).output <;> simp [wordTape,SumStacks.merge,h]
    | inr k => simp [wordTape,SumStacks.merge]
  | inr k =>
    simp [initList,SumStacks.merge]
    intro h
    subst k
    rfl

theorem preparation_run (a : α) (log : List Bool) :
    (machine w).run ((prepareComputes w).outputs a).steps
      (log,initList (computer w) (ea.encode a)) =
      some (log,phaseCfg w 0
        (Holant.Algebraic.frame (ea.encode a) ++
          List.replicate (Holant.LocalDrafts.CountingHardness.VerifierRun.witnessLength w a) true) [] []) := by
  rw [← initial_eq]
  have h := preparation_run_lift w ((prepareComputes w).outputs a).steps log _ _
    ((prepareComputes w).outputs a).evals_in_steps
  rw [preparation_halt] at h
  simpa only [preparedEncoding,pairEncoding_encode,prepared,Frame.wordEncoding,
    UnaryBinary.unaryEncoding,id_eq] using h

def verifierInput (word choices : List Bool) : List (w.verifier.tm.Γ w.verifier.tm.k₀) :=
  word.map (fun b => w.verifier.inputAlphabet.symm (Sum.inl b)) ++
    choices.reverse.map (fun b => w.verifier.inputAlphabet.symm (Sum.inr b))

theorem terminal_list (a : α) (choices : List Bool)
    (hlen : choices.length = Holant.LocalDrafts.CountingHardness.VerifierRun.witnessLength w a) :
    (Holant.LocalDrafts.CountingHardness.VerifierRun.holdStep w.verifier.tm)^[Holant.LocalDrafts.CountingHardness.VerifierRun.horizon w a]
      (initList w.verifier.tm (verifierInput w (ea.encode a) choices)) =
        haltList w.verifier.tm [w.verifier.outputAlphabet.symm
          (Sum.inr (w.accept (a,choices.reverse)))] := by
  apply Holant.LocalDrafts.CountingHardness.VerifierRun.outputs_at_bound
  have htime : w.verifier.time.eval
      (((encodingProd ea (encodingList Bool)).encode (a,choices.reverse)).length) =
        Holant.LocalDrafts.CountingHardness.VerifierRun.horizon w a := by
    rw [encodingProd_length]
    change w.verifier.time.eval ((ea.encode a).length + choices.reverse.length) =
      Holant.LocalDrafts.CountingHardness.VerifierRun.horizon w a
    rw [List.length_reverse,hlen]
    simp only [Holant.LocalDrafts.CountingHardness.VerifierRun.horizon,Holant.LocalDrafts.CountingHardness.VerifierRun.horizonPolynomial,Polynomial.eval_comp,
      Polynomial.eval_add,Polynomial.eval_X,Holant.LocalDrafts.CountingHardness.VerifierRun.witnessLength]
  have hinput :
      (((encodingProd ea (encodingList Bool)).encode (a,choices.reverse)).map
        w.verifier.inputAlphabet.symm) = verifierInput w (ea.encode a) choices := by
    simp [verifierInput,encodingProd,encodingList,List.map_append,List.map_map,Function.comp_def]
  have ht := w.verifier.outputsFun (a,choices.reverse)
  change TM2OutputsInTime w.verifier.tm
    (((encodingProd ea (encodingList Bool)).encode (a,choices.reverse)).map
      w.verifier.inputAlphabet.symm)
    (some [w.verifier.outputAlphabet.symm (Sum.inr (w.accept (a,choices.reverse)))])
    (w.verifier.time.eval
      (((encodingProd ea (encodingList Bool)).encode (a,choices.reverse)).length)) at ht
  rw [hinput,htime] at ht
  exact ht

/-- Exact physical transitions, before unique halt padding. -/
def executionSteps (a : α) : ℕ := ((prepareComputes w).outputs a).steps +
  2 * (ea.encode a).length + 2 * Holant.LocalDrafts.CountingHardness.VerifierRun.witnessLength w a + 4 + Holant.LocalDrafts.CountingHardness.VerifierRun.horizon w a

def terminal (b : Bool) : (machine w).Config :=
  verifierCfg w (haltList w.verifier.tm [w.verifier.outputAlphabet.symm (Sum.inr b)])

theorem terminal_eq_halt (b : Bool) :
    terminal w b = haltList (computer w) [w.verifier.outputAlphabet.symm (Sum.inr b)] := by
  simp only [terminal,verifierCfg,SumStacks.rightCfg,Option.map_none,verifierStates,
    haltList,computer,initial]
  congr 1
  funext key
  cases key with
  | inl k => simp [SumStacks.merge]
  | inr k =>
    by_cases h : k = w.verifier.tm.k₁
    · subst k; simp [SumStacks.merge]
    · simp [SumStacks.merge,h]

theorem full_run (a : α) (choices rest : List Bool)
    (hlen : choices.length = Holant.LocalDrafts.CountingHardness.VerifierRun.witnessLength w a) :
    (machine w).run (executionSteps w a)
      (choices ++ rest,initList (computer w) (ea.encode a)) =
        some (rest,terminal w (w.accept (a,choices.reverse))) := by
  have htime : executionSteps w a = Holant.LocalDrafts.CountingHardness.VerifierRun.horizon w a +
    (1 + ((ea.encode a).length + 1 +
      (2 * choices.length + 1 + ((ea.encode a).length + 1 +
        ((prepareComputes w).outputs a).steps)))) := by
    unfold executionSteps
    rw [hlen]
    omega
  rw [htime,BinaryMachine.run_add,BinaryMachine.run_add,BinaryMachine.run_add,
    BinaryMachine.run_add,BinaryMachine.run_add,preparation_run,Option.bind_some,
    scan_run,Option.bind_some]
  simp only [List.append_nil]
  rw [← hlen,choice_run,Option.bind_some]
  simp only [List.append_nil]
  have hc := copy_run w (ea.encode a).reverse rest
    (choices.reverse.map (fun b => w.verifier.inputAlphabet.symm (Sum.inr b)))
  simp only [List.length_reverse,List.reverse_reverse] at hc
  rw [hc,Option.bind_some]
  rw [BinaryMachine.run_one,launch,Option.bind_some]
  rw [verifier_run,← verifierInput,terminal_list w a choices hlen]
  rfl

end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.WitnessMachine
