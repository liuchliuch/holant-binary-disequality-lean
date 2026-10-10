import Holant.Proofs.AlgebraicRecognition.WitnessOutput.ReturnedRootBranchSelection.Catalogue


namespace Holant.LocalDrafts.EffectiveAlgebraic.WitnessOutput.ReturnedRootBranchSelection
open Polynomial Turing Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open GraphPreprocessing UniversalPairReduction.SmoothingCompiler FixedGadgetSubstitution.Compiler
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.Tractability.AffineMachine
open CommonFieldMachine (Executes)
open ComplexIsolation

namespace Bounded
abbrev Verdict := Bool × Bool
def ofValues (bs : List Bool) : Verdict := (decide (bs≠[]),bs.getD 0 false)
def verdict (c : RootCode) (q : Code.Poly) (es : List Evidence) : Verdict :=
  ofValues (Scan.values (c,q) es)
def rowVerdict (o : Output) (es : List Evidence) (p : Evaluate.Row) : Verdict :=
  verdict o.root (Evaluate.row o.variables p) es
def bodyVerdict (o : Output) (es : List Evidence) (S : Evaluate.Body) : Verdict :=
  let vs := S.map (rowVerdict o es)
  (vs.all Prod.fst,vs.all Prod.snd)
def step {B : Type} (o : Output) (es : List Evidence) (e : Entry B)
    (rest : Bool × Option B) : Bool × Option B :=
  let v := bodyVerdict o es e.2
  if v.1 then (if v.2 then (true,some e.1) else rest) else (false,none)
def select {B : Type} (o : Output) (es : List Evidence) (cs : Catalogue B) : Bool × Option B :=
  cs.foldr (step o es) (true,none)
def packet {B : Type} (o : Output) (es : List Evidence) (cs : Catalogue B) : Output × (Bool × Option B) :=
  (o,select o es cs)
@[simp] theorem packet_payload {B : Type} (o : Output) (es : List Evidence) (cs : Catalogue B) :
    (packet o es cs).1=o := rfl

theorem verdict_sound (c : RootCode) (q : Code.Poly) (hv : Valid c) (es : List Evidence)
    (hk : (verdict c q es).1=true) : (verdict c q es).2=zeroPolynomial c q hv := by
  have hv' : Valid c := hv
  obtain ⟨z,hz⟩ := hv'
  change (Scan.values (c,q) es).getD 0 false=zeroPolynomial c q hv
  cases hs : Scan.values (c,q) es with
  | nil => simp [verdict,ofValues,hs] at hk
  | cons b bs =>
    have hfirst : Scan.first (c,q) es=some b := by simp [Scan.first,hs]
    have hsound := Scan.first_sound hz hfirst
    change b=zeroPolynomial c q hv
    apply Bool.eq_iff_iff.mpr
    exact hsound.trans (zeroPolynomial_iff c q hv z hz).symm

theorem bodyVerdict_sound (o : Output) (hv : Valid o.root) (es : List Evidence)
    (S : Evaluate.Body) (hk : (bodyVerdict o es S).1=true) :
    (bodyVerdict o es S).2=passes o hv S := by
  have known : ∀ p ∈ S, (rowVerdict o es p).1=true := by
    simpa only [bodyVerdict,List.all_map,List.all_eq_true,Function.comp_def] using hk
  apply Bool.eq_iff_iff.mpr
  simp only [bodyVerdict,List.all_map,List.all_eq_true,Function.comp_def,passes]
  constructor <;> intro h p hp
  · simpa only [rowVerdict,verdict_sound o.root (Evaluate.row o.variables p) hv es (known p hp)] using h p hp
  · simpa only [rowVerdict,verdict_sound o.root (Evaluate.row o.variables p) hv es (known p hp)] using h p hp

/-- Known output is exactly the source first-match result, not merely some
correct later branch. The proof uses the verifier theorem, never a supplied
zero-comparison correctness assumption. -/
theorem select_sound {B : Type} (o : Output) (hv : Valid o.root) (es : List Evidence)
    (cs : Catalogue B) (hk : (select o es cs).1=true) :
    (select o es cs).2=first o hv cs := by
  induction cs with
  | nil => rfl
  | cons e es' ih =>
    rcases e with ⟨b,S⟩
    cases hknown : (bodyVerdict o es S).1 with
    | false => simp [select,step,hknown] at hk
    | true =>
      have heq := bodyVerdict_sound o hv es S hknown
      cases hvalue : (bodyVerdict o es S).2 with
      | true => simp [select,step,hknown,hvalue,first,←heq]
      | false =>
        have hrest : (select o es es').1=true := by simpa [select,step,hknown,hvalue] using hk
        simpa [select,step,hknown,hvalue,first,←heq] using ih hrest

theorem verdict_known_of_evidence (c : RootCode) (q : Code.Poly) (es : List Evidence)
    (he : ∃ e ∈ es, check c q e=true) : (verdict c q es).1=true := by
  obtain ⟨e,he,hcheck⟩ := he
  have hm : e.zero ∈ Scan.values (c,q) es := Scan.mem_values.mpr ⟨e,he,hcheck,rfl⟩
  simp only [verdict,ofValues,decide_eq_true_eq]
  intro hn
  simpa only [hn,List.not_mem_nil] using hm

/-- Finite simultaneous coverage. This existential proof is not an executable
Evidence-table producer and is not supplied to any of the machines below. -/
theorem exists_evidence_table (c : RootCode) (hv : Valid c) (qs : List Code.Poly) :
    ∃ es : List Evidence, ∀ q ∈ qs, ∃ e ∈ es, check c q e=true := by
  obtain ⟨z,hz⟩ := hv
  induction qs with
  | nil => exact ⟨[],by simp⟩
  | cons q qs ih =>
    obtain ⟨e,he⟩ := check_complete hz q
    obtain ⟨es,hes⟩ := ih
    refine ⟨e::es,?_⟩
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨e,List.mem_cons_self,he⟩
    · obtain ⟨d,hd,hcheck⟩ := hes p hp
      exact ⟨d,List.mem_cons_of_mem _ hd,hcheck⟩

theorem select_known {B : Type} (o : Output) (es : List Evidence) (cs : Catalogue B)
    (hknown : ∀ e ∈ cs, (bodyVerdict o es e.2).1=true) : (select o es cs).1=true := by
  induction cs with
  | nil => rfl
  | cons e es' ih =>
    have hk := hknown e List.mem_cons_self
    have hr := ih (fun d hd => hknown d (List.mem_cons_of_mem _ hd))
    change (step o es e (select o es es')).1=true
    cases hv : (bodyVerdict o es e.2).2 <;> simp [step,hk,hv,hr]

theorem finite_complete {B : Type} (o : Output) (hv : Valid o.root) (cs : Catalogue B) :
    ∃ es : List Evidence, select o es cs=(true,first o hv cs) := by
  let qs := cs.flatMap (fun e => Evaluate.body o e.2)
  obtain ⟨es,hes⟩ := exists_evidence_table o.root hv qs
  have hk : ∀ e ∈ cs, (bodyVerdict o es e.2).1=true := by
    intro e he
    simp only [bodyVerdict,List.all_map,List.all_eq_true,Function.comp_def]
    intro p hp
    apply verdict_known_of_evidence
    apply hes
    apply List.mem_flatMap.mpr
    refine ⟨e,he,?_⟩
    exact List.mem_map.mpr ⟨p,hp,rfl⟩
  have known := select_known o es cs hk
  exact ⟨es,Prod.ext known (select_sound o hv es cs known)⟩

abbrev contextEncoding := pairEncoding outputEncoding Scan.evidenceListEncoding
abbrev Context := Output × List Evidence
abbrev verdictEncoding := pairEncoding encodingBoolBool encodingBoolBool
abbrev verdictsEncoding := framedListEncoding verdictEncoding
noncomputable section

def ofValuesComputes : Computes Scan.valuesEncoding verdictEncoding ofValues := by
  let length := (WireLists.lengthComputes encodingBoolBool).andThen GraphPreprocessing.UnaryBinary.computes
  let empty := AccessPrograms.eqNat length (constantComputes Scan.valuesEncoding encodingNatBool 0)
  let known := empty.andThen Holant.LocalDrafts.Tractability.ProductMachine.Rewrite.negComputes
  let value := getDComputes encodingBoolBool 0 false
  exact congrComputes (pairComputes known value) (fun xs => by
    cases xs <;> simp [ofValues])

def outputRoot : Computes outputEncoding CertificateMachine.rootEncoding Output.root :=
  recode (Wiring.firstComputes CertificateMachine.rootEncoding
    (pairEncoding CommonFieldMachine.coordinatesEncoding (pairEncoding quadEncoding
      (pairEncoding quadEncoding (pairEncoding PositiveCertificateMachine.vectorsEncoding
        PositiveCertificateMachine.vectorsEncoding)))))
      Output.wire (fun _ => rfl) (fun _ => rfl)

abbrev rowInputEncoding := pairEncoding contextEncoding RationalInputMachine.rowEncoding
def rowExecutes : Executes rowInputEncoding verdictEncoding (fun p : Context × Evaluate.Row => rowVerdict p.1.1 p.1.2 p.2) := by
  let ctx := Wiring.firstComputes contextEncoding RationalInputMachine.rowEncoding
  let p := Wiring.secondComputes contextEncoding RationalInputMachine.rowEncoding
  let o := ctx.andThen (Wiring.firstComputes outputEncoding Scan.evidenceListEncoding)
  let es := ctx.andThen (Wiring.secondComputes outputEncoding Scan.evidenceListEncoding)
  let polynomial := (Executes.ofComputes (pairComputes
    (o.andThen BranchConsumers.variablesComputes) p)).comp Evaluate.rowExecutes
  let source := (Executes.ofComputes (o.andThen outputRoot)).pair polynomial
  let scan := (source.pair (Executes.ofComputes es)).comp Scan.valuesExecutes
  exact scan.comp (Executes.ofComputes ofValuesComputes)

def verdictsComputes : Computes verdictsEncoding verdictEncoding
    (fun vs : List Verdict => (vs.all Prod.fst,vs.all Prod.snd)) := by
  let w := pairComputes
    ((WireLists.mapComputes verdictEncoding encodingBoolBool Prod.fst (Wiring.firstComputes _ _)).andThen
      CommonFieldMachine.CoordinatePrimitives.allTrue)
    ((WireLists.mapComputes verdictEncoding encodingBoolBool Prod.snd (Wiring.secondComputes _ _)).andThen
      CommonFieldMachine.CoordinatePrimitives.allTrue)
  exact congrComputes w (fun vs => by simp only [List.all_map,Function.comp_def,id_eq])
abbrev bodyInputEncoding := pairEncoding contextEncoding RationalInputMachine.bodyEncoding
def bodyExecutes : Executes bodyInputEncoding verdictEncoding
    (fun p : Context × Evaluate.Body => bodyVerdict p.1.1 p.1.2 p.2) :=
  (Executes.mapList contextEncoding RationalInputMachine.rowEncoding verdictEncoding
    (fun c p => rowVerdict c.1 c.2 p) rowExecutes).comp (Executes.ofComputes verdictsComputes)

abbrev resultEncoding {B : Type} (eb : Encoding B Bool) := pairEncoding encodingBoolBool
  (Holant.OneHot.StackProgram.GraphLabelEncoding.optionEncoding eb)

def someComputes {B : Type} (eb : Encoding B Bool) : Computes eb
    (Holant.OneHot.StackProgram.GraphLabelEncoding.optionEncoding eb) (fun b => some b) :=
  recode (joinComputes (constantComputes eb Frame.wordEncoding [true]) (encodeComputes eb))
    id (fun _ => rfl) (fun _ => rfl)

def selectCell {B : Type} (eb : Encoding B Bool) :
    Computes (pairEncoding verdictEncoding (pairEncoding eb (resultEncoding eb))) (resultEncoding eb)
      (fun p : Verdict × (B × (Bool × Option B)) =>
        if p.1.1 then (if p.1.2 then (true,some p.2.1) else p.2.2) else (false,none)) := by
  let input := pairEncoding verdictEncoding (pairEncoding eb (resultEncoding eb))
  let v := Wiring.firstComputes verdictEncoding (pairEncoding eb (resultEncoding eb))
  let rest := Wiring.secondComputes verdictEncoding (pairEncoding eb (resultEncoding eb))
  let known := v.andThen (Wiring.firstComputes _ _)
  let value := v.andThen (Wiring.secondComputes _ _)
  let code := rest.andThen (Wiring.firstComputes eb (resultEncoding eb))
  let accumulator := rest.andThen (Wiring.secondComputes eb (resultEncoding eb))
  let accepted := pairComputes (constantComputes input encodingBoolBool true)
    (code.andThen (someComputes eb))
  exact ifComputes known (ifComputes value accepted accumulator)
    (constantComputes input (resultEncoding eb) (false,none))

def stepExecutes {B : Type} (eb : Encoding B Bool) :
    Executes (pairEncoding contextEncoding (pairEncoding (entryEncoding eb) (resultEncoding eb)))
      (resultEncoding eb) (fun p : Context × (Entry B × (Bool × Option B)) => step p.1.1 p.1.2 p.2.1 p.2.2) := by
  let input := pairEncoding contextEncoding (pairEncoding (entryEncoding eb) (resultEncoding eb))
  let ctx := Wiring.firstComputes contextEncoding (pairEncoding (entryEncoding eb) (resultEncoding eb))
  let rest := Wiring.secondComputes contextEncoding (pairEncoding (entryEncoding eb) (resultEncoding eb))
  let entry := rest.andThen (Wiring.firstComputes _ _)
  let code := entry.andThen (Wiring.firstComputes eb RationalInputMachine.bodyEncoding)
  let rows := entry.andThen (Wiring.secondComputes eb RationalInputMachine.bodyEncoding)
  let accumulator := rest.andThen (Wiring.secondComputes _ _)
  let v := (Executes.ofComputes (pairComputes ctx rows)).comp bodyExecutes
  exact (v.pair (Executes.ofComputes (pairComputes code accumulator))).comp
    (Executes.ofComputes (selectCell eb))

def selectExecutes {B : Type} (eb : Encoding B Bool) (default : B) :
    Executes (pairEncoding contextEncoding (catalogueEncoding eb)) (resultEncoding eb)
      (fun p : Context × Catalogue B => select p.1.1 p.1.2 p.2) := by
  let input := pairEncoding contextEncoding (catalogueEncoding eb)
  let ctx := Wiring.firstComputes contextEncoding (catalogueEncoding eb)
  let cs := Wiring.secondComputes contextEncoding (catalogueEncoding eb)
  let seed := constantComputes input (resultEncoding eb) (true,none)
  let start := Executes.ofComputes (pairComputes ctx (pairComputes cs seed))
  exact start.comp (PositiveCertificateMachine.RightFold.executes contextEncoding
    (entryEncoding eb) (resultEncoding eb) (fun c e rest => step c.1 c.2 e rest) (default,[])
      (stepExecutes eb))

def packetExecutes {B : Type} (eb : Encoding B Bool) (default : B) :
    Executes (pairEncoding contextEncoding (catalogueEncoding eb))
      (pairEncoding outputEncoding (resultEncoding eb))
      (fun p : Context × Catalogue B => packet p.1.1 p.1.2 p.2) :=
  (Executes.ofComputes ((Wiring.firstComputes contextEncoding (catalogueEncoding eb)).andThen
    (Wiring.firstComputes outputEncoding Scan.evidenceListEncoding))).pair (selectExecutes eb default)
end
end Bounded
end Holant.LocalDrafts.EffectiveAlgebraic.WitnessOutput.ReturnedRootBranchSelection
