import Holant.Proofs.AlgebraicRecognition.WitnessOutput.ReturnedRootBranchSelection.PhysicalSearch.Stage
import Holant.Proofs.Algorithms.TransformRecognition.CertificateSearchLoop


namespace Holant.LocalDrafts.EffectiveAlgebraic.WitnessOutput.ReturnedRootBranchSelection.PhysicalSearch.Controller
open Turing Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.MainChain.TransformRecognition
open CommonFieldMachine (Executes)

abbrev State := Request × Option Bool
abbrev encoding := pairEncoding requestEncoding Scan.resultEncoding
def bump (r : Request) : Request := (r.1,r.2+1)
def advance (r : Request) (n : ℕ) : Request := (bump^[n]) r
def bodyValue (s : State) : Bool × State := ((stage s.1).isNone,bump s.1,stage s.1)

theorem advance_eq (r : Request) (n : ℕ) : advance r n=(r.1,r.2+n) := by
  induction n with
  | zero => simp only [advance,Function.iterate_zero_apply,Nat.add_zero]
  | succ n ih =>
    rw [advance,Function.iterate_succ_apply']
    change bump (advance r n)=_
    rw [ih]
    simp only [bump,Nat.add_assoc]

@[simp] theorem advance_context (r : Request) (n : ℕ) : (advance r n).1=r.1 := by rw [advance_eq]

noncomputable section

def bumpExecutes : Executes requestEncoding requestEncoding bump :=
  (Executes.ofComputes (Wiring.firstComputes contextEncoding encodingNatBool)).pair
    ((Executes.ofComputes (Wiring.secondComputes contextEncoding encodingNatBool)).comp
      NegativeCatalogueMachine.Programs.successor)

def body : Executes encoding (pairEncoding encodingBoolBool encoding) bodyValue := by
  let request := Executes.ofComputes (Wiring.firstComputes requestEncoding Scan.resultEncoding)
  let next := Executes.pair (request.comp bumpExecutes) (request.comp stageExecutes)
  let flag := (Wiring.secondComputes requestEncoding Scan.resultEncoding).andThen
    CertificateSearchLoop.noneComputes
  let pack := Executes.ofComputes (pairComputes flag (identityComputes encoding))
  exact ((next.comp pack).congr (fun _ => rfl)).comp
    (Executes.ofComputes (identityComputes (pairEncoding encodingBoolBool encoding)))

theorem disjoint : body.machine.output ≠ body.machine.input := by intro h; cases h

/-- Literal reuse of the existing controller, not a newly defined TM2 loop. -/
def loop := CommonFieldMachine.ReturningLoop.machine body.machine

def bound : ℕ → State → ℕ
  | 0,s => body.cost s+2*(encoding.encode (bump s.1,stage s.1)).length+4
  | n+1,s => body.cost s+2*(encoding.encode (bump s.1,stage s.1)).length+3+
      bound n (bump s.1,stage s.1)

/-- These local first-stage premises are discharged by first_success in
total below. Neither is an encoded input or a premise of the final source. -/
theorem run (n : ℕ) (r : Request) (old : Option Bool) (b : Bool)
    (before : ∀ j < n, stage (advance r j)=none)
    (last : stage (advance r n)=some b) :
    ∃ ticks, ticks ≤ bound n (r,old) ∧
      StackProtocol.RunsExactly loop.computer.step
        (CommonFieldMachine.ReturningLoop.ready body.machine (.inl body.machine.main)
          (.inl body.machine.input) (encoding.encode (r,old)))
        (haltList loop.computer (encoding.encode (advance r (n+1),some b))) ticks := by
  induction n generalizing r old with
  | zero =>
    have hs : stage r=some b := last
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
    have hs : stage r=none := before 0 (Nat.zero_lt_succ n)
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
    have hb : ∀ j < n, stage (advance (bump r) j)=none := by
      intro j hj
      simpa only [advance,Function.iterate_succ_apply] using before (j+1) (Nat.succ_lt_succ hj)
    have hl : stage (advance (bump r) n)=some b := by
      simpa only [advance,Function.iterate_succ_apply] using last
    obtain ⟨t,ht,rest⟩ := ih (bump r) none hb hl
    refine ⟨t+(o.steps+2*(encoding.encode (bump r,none)).length+3),?_,?_⟩
    · have ho := o.steps_le_m
      simp only [bound,hs]
      omega
    · have hrun := first.trans rest
      simp only [advance,Function.iterate_succ_apply] at hrun ⊢
      exact hrun

def prepare : Computes contextEncoding encoding (fun x : Context => ((x,0),none)) :=
  pairComputes (pairComputes (identityComputes contextEncoding)
    (constantComputes contextEncoding encodingNatBool 0))
    (constantComputes contextEncoding Scan.resultEncoding none)

def extract : Computes encoding encodingBoolBool (fun s : State => s.2.getD false) :=
  (Wiring.secondComputes requestEncoding Scan.resultEncoding).andThen CertificateSearchLoop.answerComputes

/-- Fixed finite control. The input is exactly (original RootCode, raw q).
Validity is erased; no successful Evidence or stopping height is supplied. -/
def machine := (prepare.machine.compose loop).compose extract.machine

def totalBound (n : ℕ) (x : Context) (b : Bool) : ℕ :=
  prepare.time.eval (contextEncoding.encode x).length+
    2*((encoding.encode ((x,0),none)).length+1)+bound n ((x,0),none)+
    2*((encoding.encode (advance (x,0) (n+1),some b)).length+1)+
      extract.time.eval (encoding.encode (advance (x,0) (n+1),some b)).length

/-- Prop-valued packaging avoids choosing proof ticks in a Type-valued
output routine. The concrete controller and finite body already exist. -/
theorem outputs_of_first (n : ℕ) (x : Context) (b : Bool)
    (before : ∀ j < n, stage (x,j)=none) (last : stage (x,n)=some b) :
    Nonempty (TM2OutputsInTime machine.computer (contextEncoding.encode x)
      (some (encodingBoolBool.encode b)) (totalBound n x b)) := by
  have hbefore : ∀ j < n, stage (advance (x,0) j)=none := by
    intro j hj
    simpa only [advance_eq,Nat.zero_add] using before j hj
  have hlast : stage (advance (x,0) n)=some b := by
    simpa only [advance_eq,Nat.zero_add] using last
  obtain ⟨ticks,hticks,hr⟩ := run n (x,0) none b hbefore hlast
  let hloop : TM2OutputsInTime loop.computer (encoding.encode ((x,0),none))
      (some (encoding.encode (advance (x,0) (n+1),some b))) (bound n ((x,0),none)) := {
    steps := ticks
    evals_in_steps := by
      change StackProtocol.RunsExactly loop.computer.step
        (initList loop.computer (encoding.encode ((x,0),none)))
        (haltList loop.computer (encoding.encode (advance (x,0) (n+1),some b))) ticks
      rw [show initList loop.computer (encoding.encode ((x,0),none)) =
        CommonFieldMachine.ReturningLoop.ready body.machine (.inl body.machine.main)
          (.inl body.machine.input) (encoding.encode ((x,0),none)) from
        CommonFieldMachine.ReturningLoop.initial body.machine _]
      exact hr
    steps_le_m := hticks }
  let start := Machine.compose_correct _ _ _ _ _ _ _ (prepare.outputs x) hloop
  exact ⟨Machine.compose_correct _ _ _ _ _ _ _ start
    (extract.outputs (advance (x,0) (n+1),some b))⟩

/-- Total termination on the represented-root domain. The first-success
premises above are produced internally from mathematical certificate coverage. -/
theorem total (x : Context) (hv : Valid x.1) :
    ∃ n b, Nonempty (TM2OutputsInTime machine.computer (contextEncoding.encode x)
      (some (encodingBoolBool.encode b)) (totalBound n x b)) ∧
      stage (x,n)=some b ∧ ∀ j < n, stage (x,j)=none := by
  obtain ⟨n,b,hl,hbefore⟩ := first_success x hv
  exact ⟨n,b,outputs_of_first n x b hbefore hl,hl,hbefore⟩

theorem total_correct (x : Context) (z : ℂ) (hz : x.1.Represents z) :
    ∃ n b, Nonempty (TM2OutputsInTime machine.computer (contextEncoding.encode x)
      (some (encodingBoolBool.encode b)) (totalBound n x b)) ∧
      (b=true ↔ Polynomial.aeval z x.2.polynomial=0) := by
  obtain ⟨n,b,hout,hl,_⟩ := total x ⟨z,hz⟩
  exact ⟨n,b,hout,stage_sound hz hl⟩

/-- Comparison with the old source-level Bool is a proof of output semantics,
not the physical implementation of its source-level indexing operation. -/
theorem source_outputs (x : Context) (hv : Valid x.1) :
    ∃ n, Nonempty (TM2OutputsInTime machine.computer (contextEncoding.encode x)
      (some (encodingBoolBool.encode (zeroPolynomial x.1 x.2 hv)))
      (totalBound n x (zeroPolynomial x.1 x.2 hv))) := by
  have hv' : Valid x.1 := hv
  obtain ⟨z,hz⟩ := hv'
  obtain ⟨n,b,hout,hl,_⟩ := total x hv
  have hb := stage_sound hz hl
  have hf := zeroPolynomial_iff x.1 x.2 hv z hz
  have he : b=zeroPolynomial x.1 x.2 hv := by
    cases b <;> cases hs : zeroPolynomial x.1 x.2 hv <;> simp_all
  exact ⟨n,by simpa only [he] using hout⟩

theorem primitives (n : ℕ) (x : Context) (b : Bool)
    (out : TM2OutputsInTime machine.computer (contextEncoding.encode x)
      (some (encodingBoolBool.encode b)) (totalBound n x b)) :
    primitiveCost machine out.steps (some (initList machine.computer (contextEncoding.encode x))) ≤
      totalBound n x b*machine.primitiveBudget :=
  (primitiveCost_le _ _ _).trans (Nat.mul_le_mul_right _ out.steps_le_m)

theorem prefix_bits (n : ℕ) (x : Context) (b : Bool)
    (out : TM2OutputsInTime machine.computer (contextEncoding.encode x)
      (some (encodingBoolBool.encode b)) (totalBound n x b))
    (j : ℕ) (hj : j ≤ out.steps) (c : machine.Config)
    (hc : (fun p => p.bind machine.computer.step)^[j]
      (some (initList machine.computer (contextEncoding.encode x)))=some c) :
    stackSize c.stk ≤ (contextEncoding.encode x).length+totalBound n x b*machine.primitiveBudget := by
  have hs := machine.run_size_le (initList machine.computer (contextEncoding.encode x)) c j hc
  rw [Machine.size_init] at hs
  exact hs.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ (hj.trans out.steps_le_m)) _)
end
end Holant.LocalDrafts.EffectiveAlgebraic.WitnessOutput.ReturnedRootBranchSelection.PhysicalSearch.Controller
