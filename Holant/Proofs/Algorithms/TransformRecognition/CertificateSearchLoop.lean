import Holant.Proofs.Algorithms.TransformRecognition.OriginalCertificateStage
import Holant.Proofs.BinaryInterpolation.EffectiveRecognition.CommonFieldMachine.ReturningLoop


namespace Holant.LocalDrafts.MainChain.TransformRecognition.CertificateSearchLoop
open Turing Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open UniversalPairReduction.SmoothingCompiler
open Holant.LocalDrafts.EffectiveAlgebraic
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open CommonFieldMachine (Executes)

abbrev Request := OriginalCertificateStage.Request
abbrev requestEncoding := OriginalCertificateStage.encoding
abbrev resultEncoding := CertificateStageMachine.resultEncoding
abbrev State := Request × Option Bool
abbrev encoding := pairEncoding requestEncoding resultEncoding

def bump (r : Request) : Request := { r with height := r.height+1 }
def advance (r : Request) (n : ℕ) : Request := (bump^[n]) r
def bodyValue (s : State) : Bool × State :=
  ((OriginalCertificateStage.stage s.1).isNone,bump s.1,OriginalCertificateStage.stage s.1)

noncomputable section

def bumpComputes : Executes requestEncoding requestEncoding bump := by
  let next := (Executes.ofComputes NegativeCatalogueMachine.Access.height).comp
    NegativeCatalogueMachine.Programs.successor
  let context := Executes.pair (Executes.ofComputes NegativeCatalogueMachine.Access.equations) next
  let roots := Executes.pair (Executes.ofComputes NegativeCatalogueMachine.Access.targets) context
  let variableCount := Executes.pair (Executes.ofComputes NegativeCatalogueMachine.Access.variables) roots
  let full := Executes.pair (Executes.ofComputes NegativeCatalogueMachine.Access.coefficients) variableCount
  exact Executes.recode full id (fun _ => rfl) (fun _ => rfl)

def noneComputes : Computes resultEncoding encodingBoolBool Option.isNone :=
  GraphPreprocessing.FiniteRecode.computes _ _ Option.isNone 2
    (fun b => by cases b with | none => decide | some b => cases b <;> decide)

def body : Executes encoding (pairEncoding encodingBoolBool encoding) bodyValue := by
  let request := Executes.ofComputes (Wiring.firstComputes requestEncoding resultEncoding)
  let next := Executes.pair (request.comp bumpComputes)
    (request.comp OriginalCertificateStage.executes)
  let flag := (Wiring.secondComputes requestEncoding resultEncoding).andThen noneComputes
  let pack := Executes.ofComputes (pairComputes flag (identityComputes encoding))
  exact ((next.comp pack).congr (fun _ => rfl)).comp
    (Executes.ofComputes (identityComputes (pairEncoding encodingBoolBool encoding)))

theorem disjoint : body.machine.output ≠ body.machine.input := by
  intro h
  cases h

def loop := CommonFieldMachine.ReturningLoop.machine body.machine

def bound : ℕ → State → ℕ
  | 0,s => body.cost s + 2*(encoding.encode (bump s.1,OriginalCertificateStage.stage s.1)).length+4
  | n+1,s => body.cost s + 2*(encoding.encode (bump s.1,OriginalCertificateStage.stage s.1)).length+3 +
      bound n (bump s.1,OriginalCertificateStage.stage s.1)

/-- A local run lemma, subsequently instantiated with the least successful
height derived from the original descriptors. Its premises are not parameters
of the machine or assumptions in the final original-input theorem. -/
theorem run (n : ℕ) (r : Request) (old : Option Bool) (b : Bool)
    (before : ∀ j < n, OriginalCertificateStage.stage (advance r j)=none)
    (last : OriginalCertificateStage.stage (advance r n)=some b) :
    ∃ ticks, ticks ≤ bound n (r,old) ∧
      StackProtocol.RunsExactly loop.computer.step
        (CommonFieldMachine.ReturningLoop.ready body.machine (.inl body.machine.main)
          (.inl body.machine.input) (encoding.encode (r,old)))
        (haltList loop.computer (encoding.encode (advance r (n+1),some b))) ticks := by
  induction n generalizing r old with
  | zero =>
    have hs : OriginalCertificateStage.stage r=some b := last
    let o := body.outputs (r,old)
    have h := CommonFieldMachine.ReturningLoop.stop_run body.machine _ _ o.steps
      (by
        have ho := o.evals_in_steps
        change StackProtocol.RunsExactly body.machine.computer.step
          (initList body.machine.computer (encoding.encode (r,old)))
          (haltList body.machine.computer
            ((pairEncoding encodingBoolBool encoding).encode (bodyValue (r,old)))) o.steps at ho
        simp only [bodyValue,hs,Option.isNone_some,pairEncoding,encodingBoolBool,encodeBool] at ho
        exact ho)
    refine ⟨o.steps+2*(encoding.encode (bump r,some b)).length+4,?_,?_⟩
    · have ho := o.steps_le_m
      simp only [bound,hs]
      omega
    · exact h
  | succ n ih =>
    have hs : OriginalCertificateStage.stage r=none := before 0 (Nat.zero_lt_succ n)
    let o := body.outputs (r,old)
    have first := CommonFieldMachine.ReturningLoop.continue_run body.machine disjoint _ _ o.steps
      (by
        have ho := o.evals_in_steps
        change StackProtocol.RunsExactly body.machine.computer.step
          (initList body.machine.computer (encoding.encode (r,old)))
          (haltList body.machine.computer
            ((pairEncoding encodingBoolBool encoding).encode (bodyValue (r,old)))) o.steps at ho
        simp only [bodyValue,hs,Option.isNone_none,pairEncoding,encodingBoolBool,encodeBool] at ho
        exact ho)
    have hb : ∀ j < n, OriginalCertificateStage.stage (advance (bump r) j)=none := by
      intro j hj
      simpa only [advance,Function.iterate_succ_apply] using before (j+1) (Nat.succ_lt_succ hj)
    have hl : OriginalCertificateStage.stage (advance (bump r) n)=some b := by
      simpa only [advance,Function.iterate_succ_apply] using last
    obtain ⟨t,ht,rest⟩ := ih (bump r) none hb hl
    refine ⟨t+(o.steps+2*(encoding.encode (bump r,none)).length+3),?_,?_⟩
    · have ho := o.steps_le_m
      simp only [bound,hs]
      omega
    · have hrun := first.trans rest
      simp only [advance,Function.iterate_succ_apply] at hrun ⊢
      exact hrun

def prepare : Computes requestEncoding encoding (fun r => (r,none)) :=
  pairComputes (identityComputes requestEncoding) (constantComputes requestEncoding resultEncoding none)

def answerComputes : Computes resultEncoding encodingBoolBool (fun b => b.getD false) :=
  GraphPreprocessing.FiniteRecode.computes _ _ (fun b : Option Bool => b.getD false) 2
    (fun b => by cases b with | none => decide | some b => cases b <;> decide)

def extract : Computes encoding encodingBoolBool (fun s => s.2.getD false) :=
  (Wiring.secondComputes requestEncoding resultEncoding).andThen answerComputes

/-- This fixed machine receives no stopping height. Malformed or invalid
descriptors are not promised to terminate. The next file proves termination
on the original valid coefficient descriptors and guarded source system. -/
def machine := (prepare.machine.compose loop).compose extract.machine

def totalBound (n : ℕ) (r : Request) (b : Bool) : ℕ :=
  prepare.time.eval (requestEncoding.encode r).length +
    2*((encoding.encode (r,none)).length+1) + bound n (r,none) +
    2*((encoding.encode (advance r (n+1),some b)).length+1) +
      extract.time.eval (encoding.encode (advance r (n+1),some b)).length

def outputs_of_first (n : ℕ) (r : Request) (b : Bool)
    (before : ∀ j < n, OriginalCertificateStage.stage (advance r j)=none)
    (last : OriginalCertificateStage.stage (advance r n)=some b) :
    TM2OutputsInTime machine.computer (requestEncoding.encode r)
      (some (encodingBoolBool.encode b)) (totalBound n r b) := by
  let execution := run n r none b before last
  let t := Classical.choose execution
  have ht := (Classical.choose_spec execution).1
  have hr := (Classical.choose_spec execution).2
  have hloop : TM2OutputsInTime loop.computer (encoding.encode (r,none))
      (some (encoding.encode (advance r (n+1),some b))) (bound n (r,none)) :=
    { steps := t
      evals_in_steps := by
        change StackProtocol.RunsExactly loop.computer.step
          (initList loop.computer (encoding.encode (r,none)))
          (haltList loop.computer (encoding.encode (advance r (n+1),some b))) t
        rw [show initList loop.computer (encoding.encode (r,none)) =
          CommonFieldMachine.ReturningLoop.ready body.machine (.inl body.machine.main)
            (.inl body.machine.input) (encoding.encode (r,none)) from
          CommonFieldMachine.ReturningLoop.initial body.machine _]
        exact hr
      steps_le_m := ht }
  have hprepare := prepare.outputs r
  have hfirst := Machine.compose_correct _ _ _ _ _ _ _ hprepare hloop
  have hend := extract.outputs (advance r (n+1),some b)
  exact Machine.compose_correct _ _ _ _ _ _ _ hfirst hend

theorem primitives_of_first (n : ℕ) (r : Request) (b : Bool)
    (before : ∀ j < n, OriginalCertificateStage.stage (advance r j)=none)
    (last : OriginalCertificateStage.stage (advance r n)=some b) :
    primitiveCost machine (outputs_of_first n r b before last).steps
      (some (initList machine.computer (requestEncoding.encode r))) ≤
        totalBound n r b*machine.primitiveBudget :=
  (primitiveCost_le _ _ _).trans
    (Nat.mul_le_mul_right _ (outputs_of_first n r b before last).steps_le_m)

theorem intermediate_bits_of_first (n : ℕ) (r : Request) (b : Bool)
    (before : ∀ j < n, OriginalCertificateStage.stage (advance r j)=none)
    (last : OriginalCertificateStage.stage (advance r n)=some b)
    (j : ℕ) (hj : j ≤ (outputs_of_first n r b before last).steps)
    (c : machine.Config)
    (hc : (fun p => p.bind machine.computer.step)^[j]
      (some (initList machine.computer (requestEncoding.encode r)))=some c) :
    stackSize c.stk ≤ (requestEncoding.encode r).length+totalBound n r b*machine.primitiveBudget := by
  have h := machine.run_size_le (initList machine.computer (requestEncoding.encode r)) c j hc
  rw [Machine.size_init] at h
  exact h.trans (Nat.add_le_add_left
    (Nat.mul_le_mul_right _ (hj.trans (outputs_of_first n r b before last).steps_le_m)) _)

end
end Holant.LocalDrafts.MainChain.TransformRecognition.CertificateSearchLoop
