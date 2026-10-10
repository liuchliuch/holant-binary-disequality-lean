import Holant.Proofs.LinearProgramming.Support.MachineCombinators
import Holant.Proofs.LinearProgramming.Recovery.RationalExtraction.Termination
import Holant.Proofs.LinearProgramming.Recovery.ExactPointRecovery.Denominator
import Holant.Complexity.FixedGadgetSubstitution.Compiler.Lists

set_option autoImplicit false

/-! Kernel-checked recovery component. Sole entry of this batch. `computes` returns the actual
2L+4-block status receipt; `extractComputes` physically emits the existing
Option rational codec. Termination proves done=true from the actual jump
potential, independently of an existence promise. Both same-machine runs have
original-word polynomial costs. This is scalar rational extraction only;
successive-face LP point recovery and the LP optimization solver are separate.
-/
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.RationalExtraction
open Holant.LocalDrafts.TraversalCompletion.RationalLP
open Holant.LocalDrafts.RemoteWork.RationalLP.Foundation
open Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators
namespace Source
open Turing Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open Holant.OneHot.StackProgram.GraphLabelEncoding
open FixedGadgetSubstitution.Compiler
noncomputable section

-- Keep the existing programme records opaque during local proof elaboration;
-- these attributes neither change their definitions nor the kernel's checks.
attribute [local irreducible] RationalExtraction.prepare Native.machine

def blockComputes : Computes queryEncoding resultEncoding Bounds.blockValue := Bounds.blockComputes
def blockMachine : Machine := blockComputes.machine
def blockTime : Polynomial ℕ := blockComputes.time
def initialized_step_input (q : Query) : StepInput := (q,Initialize.initialNeighbors q)
def stepComputes := Programs.computes

private def prepared_output {A B : Type} {ea : Encoding A Bool} {eb : Encoding B Bool}
    {f : A → B} (M : Computes ea eb f) (N : Machine) (g : B → B) (clock : B → ℕ)
    (receipt : ∀ b, TM2OutputsInTime N.computer (eb.encode b)
      (some (eb.encode (g b))) (clock b)) (a : A) :
    TM2OutputsInTime (M.machine.compose N).computer (ea.encode a)
      (some (eb.encode (g (f a))))
      (M.time.eval (ea.encode a).length+2*((eb.encode (f a)).length+1)+clock (f a)) :=
  Machine.compose_correct M.machine N (ea.encode a) (eb.encode (f a)) (eb.encode (g (f a)))
    (M.time.eval (ea.encode a).length) (clock (f a)) (M.outputs a) (receipt (f a))

private def postprocess_output {A B : Type} {ea : Encoding A Bool} {eb : Encoding B Bool}
    {f : A → B} (M : Machine) (N : Computes ea eb f) (input : List Bool) (a : A) (ticks : ℕ)
    (receipt : TM2OutputsInTime M.computer input (some (ea.encode a)) ticks) :
    TM2OutputsInTime (M.compose N.machine).computer input (some (eb.encode (f a)))
      (ticks+2*((ea.encode a).length+1)+N.time.eval (ea.encode a).length) :=
  Machine.compose_correct M N.machine input (ea.encode a) (eb.encode (f a))
    ticks (N.time.eval (ea.encode a).length) receipt (N.outputs a)

private def encoded_output_transport {A : Type} (M : Machine) (e : Encoding A Bool)
    (input : List Bool) (x y : A) (n k : ℕ) (hx : x=y) (hn : n=k)
    (receipt : TM2OutputsInTime M.computer input (some (e.encode x)) n) :
    TM2OutputsInTime M.computer input (some (e.encode y)) k := by
  cases hx
  cases hn
  exact receipt

def stateMachine : Machine := prepare.machine.compose Native.machine
attribute [local irreducible] stateMachine
def stateTime (q : Query) : ℕ := prepare.time.eval (queryEncoding.encode q).length+
  2*((stateEncoding.encode (initial q)).length+1)+Native.ticks (rounds q) («at» q 0)
private theorem prepared_result (q : Query) : finish (initial q).1 (initial q).2=resultState q := by
  unfold initial resultState
  rfl
private theorem prepared_clock (q : Query) :
    prepare.time.eval (queryEncoding.encode q).length+2*((stateEncoding.encode (initial q)).length+1)+
      Native.ticks (initial q).1 (initial q).2=stateTime q := by
  unfold stateTime initial
  rfl
private def prepared_receipt (q : Query) :
    TM2OutputsInTime (prepare.machine.compose Native.machine).computer (queryEncoding.encode q)
      (some (stateEncoding.encode (finish (initial q).1 (initial q).2)))
      (prepare.time.eval (queryEncoding.encode q).length+2*((stateEncoding.encode (initial q)).length+1)+
        Native.ticks (initial q).1 (initial q).2) :=
  prepared_output prepare Native.machine
    (fun s : RationalExtraction.State => finish s.1 s.2)
    (fun s : RationalExtraction.State => Native.ticks s.1 s.2) Native.outputs q
def stateOutput (q : Query) : TM2OutputsInTime stateMachine.computer (queryEncoding.encode q)
    (some (stateEncoding.encode (resultState q))) (stateTime q) := by
  unfold stateMachine
  exact encoded_output_transport (prepare.machine.compose Native.machine) stateEncoding
    (queryEncoding.encode q) _ _ _ _ (prepared_result q) (prepared_clock q) (prepared_receipt q)
def project : Computes stateEncoding resultEncoding (fun s : RationalExtraction.State => s.2.2) :=
  (Wiring.secondComputes _ _).andThen (Wiring.secondComputes _ _)
attribute [local irreducible] project
def machine : Machine := stateMachine.compose project.machine
def time (q : Query) : ℕ := stateTime q+2*((stateEncoding.encode (resultState q)).length+1)+
  project.time.eval (stateEncoding.encode (resultState q)).length
private theorem projected_result (q : Query) : (resultState q).2.2=value q := by
  unfold value
  rfl
private theorem projected_clock (q : Query) :
    stateTime q+2*((stateEncoding.encode (resultState q)).length+1)+
      project.time.eval (stateEncoding.encode (resultState q)).length=time q := by
  unfold time
  rfl
private def projected_receipt (q : Query) :
    TM2OutputsInTime (stateMachine.compose project.machine).computer (queryEncoding.encode q)
      (some (resultEncoding.encode ((resultState q).2.2)))
      (stateTime q+2*((stateEncoding.encode (resultState q)).length+1)+
        project.time.eval (stateEncoding.encode (resultState q)).length) :=
  postprocess_output (ea := stateEncoding) (eb := resultEncoding)
    (f := fun s : RationalExtraction.State => s.2.2) stateMachine project
    (queryEncoding.encode q) (resultState q) (stateTime q) (stateOutput q)
def output (q : Query) : TM2OutputsInTime machine.computer (queryEncoding.encode q)
    (some (resultEncoding.encode (value q))) (time q) := by
  unfold machine
  exact encoded_output_transport (stateMachine.compose project.machine) resultEncoding
    (queryEncoding.encode q) _ _ _ _ (projected_result q) (projected_clock q) (projected_receipt q)

/-- Only the structural interval promise is proof data. Its literal bytes are
the original canonical endpoints and binary D, with no recovered answer field. -/
abbrev Input := {q : Query // Isolating q}
def inputEncoding : Encoding Input Bool where
  encode q := queryEncoding.encode q.val
  decode bits := do
    let q ← queryEncoding.decode bits
    if h : Isolating q then Option.some ⟨q,h⟩ else Option.none
  decode_encode q := by simp [q.property]
@[simp] theorem original_bytes (q : Input) : inputEncoding.encode q=queryEncoding.encode q.val := rfl
def timePolynomial : Polynomial ℕ := prepare.time+4*(GlobalBounds.stateWidth+1)+
  GlobalBounds.loopTime+project.time.comp GlobalBounds.stateWidth

private theorem initial_word_bound (q : Query) (hq : Valid q) :
    (stateEncoding.encode (initial q)).length≤GlobalBounds.stateWidth.eval (queryEncoding.encode q).length := by
  simpa only [initial] using
    GlobalBounds.actual_state_word q hq 0 (rounds q) (Nat.zero_le _) le_rfl

private theorem encoded_word_le {A : Type} (e : Encoding A Bool) (x y : A) (B : ℕ)
    (he : x=y) (hy : (e.encode y).length≤B) : (e.encode x).length≤B := by
  cases he
  exact hy

private theorem final_word_bound (q : Query) (hq : Valid q) :
    (stateEncoding.encode (resultState q)).length≤GlobalBounds.stateWidth.eval (queryEncoding.encode q).length := by
  exact encoded_word_le stateEncoding (resultState q) (0,«at» q (rounds q))
    (GlobalBounds.stateWidth.eval (queryEncoding.encode q).length) (result_exact q)
    (GlobalBounds.actual_state_word q hq (rounds q) 0 le_rfl (Nat.zero_le _))

private theorem timing_arithmetic (P I F T R W B C : ℕ)
    (hi : I≤W) (hf : F≤W) (ht : T≤B) (hp : R≤C) :
    P+2*(I+1)+T+2*(F+1)+R≤P+4*(W+1)+B+C := by omega

theorem time_le_polynomial (q : Query) (hq : Valid q) : time q≤
    timePolynomial.eval (queryEncoding.encode q).length := by
  have hi := initial_word_bound q hq
  have hf := final_word_bound q hq
  have ht := GlobalBounds.initial_ticks q hq
  have hp := natPolynomial_eval_mono project.time hf
  have h := timing_arithmetic (prepare.time.eval (queryEncoding.encode q).length)
    (stateEncoding.encode (initial q)).length (stateEncoding.encode (resultState q)).length
    (Native.ticks (rounds q) («at» q 0)) (project.time.eval (stateEncoding.encode (resultState q)).length)
    (GlobalBounds.stateWidth.eval (queryEncoding.encode q).length)
    (GlobalBounds.loopTime.eval (queryEncoding.encode q).length)
    (project.time.eval (GlobalBounds.stateWidth.eval (queryEncoding.encode q).length)) hi hf ht hp
  simpa only [time,stateTime,timePolynomial,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_ofNat,Polynomial.eval_one,Polynomial.eval_comp] using h
def computes : Computes inputEncoding resultEncoding (fun q : Input => value q.val) where
  machine := machine
  time := timePolynomial
  outputs q := {
    steps := (output q.val).steps
    evals_in_steps := (output q.val).evals_in_steps
    steps_le_m := (output q.val).steps_le_m.trans (time_le_polynomial q.val q.property.1) }
private theorem computes_time_eq : computes.time=timePolynomial := rfl
private theorem computes_machine_eq : computes.machine=machine := rfl
def primitivePolynomial : Polynomial ℕ := FixedFieldMachines.primitivePolynomial computes
def temporaryPolynomial : Polynomial ℕ := Polynomial.X+primitivePolynomial
theorem full_time (q : Input) : (computes.outputs q).steps≤
    timePolynomial.eval (inputEncoding.encode q).length := (computes.outputs q).steps_le_m
theorem full_word (q : Input) : (resultEncoding.encode (value q.val)).length≤
    computes.outputBound.bound.eval (inputEncoding.encode q).length := computes.outputBound.length_le q
theorem full_primitive (q : Input) :
    primitiveCost machine (computes.outputs q).steps
      (some (initList machine.computer (inputEncoding.encode q)))≤
        primitivePolynomial.eval (inputEncoding.encode q).length := computes_primitive_cost computes q
theorem full_temporary (q : Input) (t : ℕ) (ht : t≤(computes.outputs q).steps) (c : machine.Config)
    (hc : (fun s => s.bind machine.computer.step)^[t]
      (some (initList machine.computer (inputEncoding.encode q)))=some c) :
    stackSize c.stk≤temporaryPolynomial.eval (inputEncoding.encode q).length := by
  have hs := machine.run_size_le _ c t hc
  rw [Machine.size_init] at hs
  apply hs.trans
  simpa only [temporaryPolynomial,primitivePolynomial,FixedFieldMachines.primitivePolynomial,
    computes_time_eq,computes_machine_eq,
    Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C] using Nat.add_le_add_left
      (Nat.mul_le_mul_right machine.primitiveBudget (ht.trans (full_time q))) _

theorem execution (q : Query) : StackProtocol.RunsExactly machine.computer.step
    (initList machine.computer (queryEncoding.encode q))
    (haltList machine.computer (resultEncoding.encode (value q))) (output q).steps :=
  (output q).evals_in_steps
theorem sound (q : Query) (hq : Valid q) (hd : done (value q)=true) (hf : found (value q)=true) :
    Candidate q (answer (value q)) := (value_safe q hq).1 hd hf
theorem none_sound (q : Query) (hq : Valid q) (hd : done (value q)=true) (hf : found (value q)=false) :
    ¬∃ r, Candidate q r := (value_safe q hq).2.1 hd hf
theorem pending_domain (q : Query) (hq : Valid q) (hd : done (value q)=false) :
    Neighbors.Brackets q (neighbors (value q)) := (value_safe q hq).2.2 hd
theorem terminated (q : Query) (hq : Valid q) : done (value q)=true := Termination.complete q hq
theorem accepted (q : Query) (hq : Valid q) : found (value q)=true ↔ ∃ r, Candidate q r := by
  constructor
  · intro hf
    exact ⟨answer (value q),sound q hq (terminated q hq) hf⟩
  · intro hex
    cases hf : found (value q) with
    | true => rfl
    | false => exact False.elim (none_sound q hq (terminated q hq) hf hex)
theorem rejected (q : Query) (hq : Valid q) : found (value q)=false ↔ ¬∃ r, Candidate q r := by
  cases hf : found (value q) with
  | false =>
    constructor
    · intro _; exact none_sound q hq (terminated q hq) hf
    · intro _; rfl
  | true =>
    have hex := (accepted q hq).mp hf
    constructor
    · intro h; cases h
    · intro h; exact False.elim (h hex)

theorem unique (q : Query) (hq : Isolating q) (a b : ℚ)
    (ha : Candidate q a) (hb : Candidate q b) : a=b :=
  ExactPointRecovery.Denominator.interval_unique (cap q) hq.1.2 (lo q) (hi q) a b
    ⟨ha.1,ha.2.1⟩ ⟨hb.1,hb.2.1⟩ ha.2.2 hb.2.2 hq.2
theorem answer_unique (q : Query) (hq : Isolating q)
    (hd : done (value q)=true) (hf : found (value q)=true) :
    ∀ r, Candidate q r → r=answer (value q) := by
  intro r hr
  exact unique q hq r _ hr (sound q hq.1 hd hf)

def scalarEncoding : Encoding (Option ℚ) Bool := optionEncoding rationalEncoding
def response (r : Result) : Option ℚ := if found r then Option.some (answer r) else Option.none
def foundComputes : Computes resultEncoding encodingBoolBool found :=
  (Wiring.firstComputes _ _).andThen (Wiring.secondComputes _ _)
def answerComputes : Computes resultEncoding rationalEncoding answer :=
  (Wiring.secondComputes _ _).andThen (Wiring.firstComputes _ _)
def someComputes : Computes resultEncoding scalarEncoding (fun r : Result => Option.some (answer r)) :=
  recode (joinComputes
    (constantComputes resultEncoding Holant.Complexity.GraphPreprocessing.Frame.wordEncoding [true])
    (answerComputes.andThen (encodeComputes rationalEncoding))) id (fun _ => rfl)
      (fun _ => rfl)
def responseComputes : Computes resultEncoding scalarEncoding response :=
  congrComputes (ifComputes foundComputes someComputes
    (constantComputes resultEncoding scalarEncoding Option.none)) (fun r => by simp [response])
def extracted (q : Input) : Option ℚ := response (value q.val)
def extractComputes : Computes inputEncoding scalarEncoding extracted := computes.andThen responseComputes
def extractor : Machine := extractComputes.machine
def extractTime : Polynomial ℕ := extractComputes.time
def extractPrimitive : Polynomial ℕ := FixedFieldMachines.primitivePolynomial extractComputes
def extractTemporary : Polynomial ℕ := Polynomial.X+extractPrimitive
private theorem extract_time_eq : extractComputes.time=extractTime := rfl
private theorem extract_machine_eq : extractComputes.machine=extractor := rfl

@[simp] theorem extractor_same_machine : extractor=machine.compose responseComputes.machine := rfl
@[simp] theorem extractor_same_clock : extractTime=timePolynomial+2*(computes.outputBound.bound+1)+
    responseComputes.time.comp computes.outputBound.bound := rfl

private theorem response_some_iff (s : Result) (r : ℚ) :
    response s=Option.some r ↔ found s=true ∧ answer s=r := by
  unfold response
  cases hf : found s <;> simp [hf]

private theorem response_none_iff (s : Result) : response s=Option.none ↔ found s=false := by
  unfold response
  cases hf : found s <;> simp [hf]

theorem some_sound (q : Input) (r : ℚ) (hr : extracted q=Option.some r) : Candidate q.val r := by
  have hs := (response_some_iff (value q.val) r).mp hr
  rw [← hs.2]
  exact sound q.val q.property.1 (terminated q.val q.property.1) hs.1
theorem none_iff (q : Input) : extracted q=Option.none ↔ ¬∃ r, Candidate q.val r :=
  (response_none_iff (value q.val)).trans (rejected q.val q.property.1)
theorem recovers (q : Input) (r : ℚ) (hr : Candidate q.val r) : extracted q=Option.some r := by
  have hf := (accepted q.val q.property.1).mpr ⟨r,hr⟩
  have ha := sound q.val q.property.1 (terminated q.val q.property.1) hf
  have he := unique q.val q.property _ r ha hr
  exact (response_some_iff (value q.val) r).mpr ⟨hf,he⟩
theorem complete (q : Input) :
    (∃ r, Candidate q.val r) ↔ ∃ r, extracted q=Option.some r ∧ Candidate q.val r := by
  constructor
  · rintro ⟨r,hr⟩
    exact ⟨r,recovers q r hr,hr⟩
  · rintro ⟨r,_,hr⟩
    exact ⟨r,hr⟩
theorem extract_execution (q : Input) : StackProtocol.RunsExactly extractor.computer.step
    (initList extractor.computer (inputEncoding.encode q))
    (haltList extractor.computer (scalarEncoding.encode (extracted q))) (extractComputes.outputs q).steps :=
  (extractComputes.outputs q).evals_in_steps
theorem extract_time_bound (q : Input) : (extractComputes.outputs q).steps≤
    extractTime.eval (inputEncoding.encode q).length := (extractComputes.outputs q).steps_le_m
theorem extract_word_bound (q : Input) : (scalarEncoding.encode (extracted q)).length≤
    extractComputes.outputBound.bound.eval (inputEncoding.encode q).length := extractComputes.outputBound.length_le q
theorem extract_primitive_bound (q : Input) :
    primitiveCost extractor (extractComputes.outputs q).steps
      (some (initList extractor.computer (inputEncoding.encode q)))≤
        extractPrimitive.eval (inputEncoding.encode q).length := computes_primitive_cost extractComputes q
theorem extract_temporary_bound (q : Input) (t : ℕ) (ht : t≤(extractComputes.outputs q).steps)
    (c : extractor.Config)
    (hc : (fun s => s.bind extractor.computer.step)^[t]
      (some (initList extractor.computer (inputEncoding.encode q)))=some c) :
    stackSize c.stk≤extractTemporary.eval (inputEncoding.encode q).length := by
  have hs := extractor.run_size_le _ c t hc
  rw [Machine.size_init] at hs
  apply hs.trans
  simpa only [extractTemporary,extractPrimitive,FixedFieldMachines.primitivePolynomial,
    extract_time_eq,extract_machine_eq,
    Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C] using Nat.add_le_add_left
      (Nat.mul_le_mul_right extractor.primitiveBudget (ht.trans (extract_time_bound q))) _

/-- Honest one-block completeness: mathematical existence prevents a false
none; an unfinished state is preserved rather than converted to Option.none. -/
theorem block_complete_or_pending (q : Query) (hq : Valid q) (hex : ∃ r, Candidate q r) :
    (done (Bounds.blockValue q)=true ∧ found (Bounds.blockValue q)=true ∧
      Candidate q (answer (Bounds.blockValue q))) ∨
    (done (Bounds.blockValue q)=false ∧ Neighbors.Brackets q (neighbors (Bounds.blockValue q))) := by
  have hs := Bounds.block_safe q hq
  cases hd : done (Bounds.blockValue q) with
  | false => exact Or.inr ⟨rfl,hs.2.2 hd⟩
  | true =>
    cases hf : found (Bounds.blockValue q) with
    | false => exact False.elim (hs.2.1 hd hf hex)
    | true => exact Or.inl ⟨rfl,rfl,hs.1 hd hf⟩

/-- Raw-query exact numerical accounting, also valid without interval promises.
The promised-domain polynomial versions are full_primitive/full_temporary. -/
theorem primitive_cost (q : Query) :
    primitiveCost machine (output q).steps
      (some (initList machine.computer (queryEncoding.encode q)))≤time q*machine.primitiveBudget :=
  (primitiveCost_le _ _ _).trans (Nat.mul_le_mul_right _ (output q).steps_le_m)
theorem temporary_bits (q : Query) (t : ℕ) (ht : t≤(output q).steps) (c : machine.Config)
    (hc : (fun s => s.bind machine.computer.step)^[t]
      (some (initList machine.computer (queryEncoding.encode q)))=some c) :
    stackSize c.stk≤(queryEncoding.encode q).length+time q*machine.primitiveBudget := by
  have hs := machine.run_size_le _ c t hc
  rw [Machine.size_init] at hs
  exact hs.trans (Nat.add_le_add_left
    (Nat.mul_le_mul_right _ (ht.trans (output q).steps_le_m)) _)

end
end Source
end Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.RationalExtraction
