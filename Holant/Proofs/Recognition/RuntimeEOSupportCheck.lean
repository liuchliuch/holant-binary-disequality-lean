import Holant.Proofs.Recognition.RuntimeEOViewSupport

/-! Finite EO domain/triple scans on an intermediate zero table. All triples
are generated internally. The output retains every concrete bad word/triple;
no caller supplies sign answers or negative certificates. The semantic table
hypothesis is for composing with RuntimeEOViewSupport, not a public original
input promise. Literal A/P checks and final EO aggregation remain separate. -/
namespace Holant.LocalDrafts.RemoteWork.TractChainV1.RuntimeEOSupportCheck
open Turing Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing UniversalPairReduction.SmoothingCompiler
open Holant.LocalDrafts.MainChain.TransformRecognition
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.EffectiveAlgebraic
open Holant.LocalDrafts.Tractability.AffineMachine
open CommonFieldMachine (Executes)
open RuntimeTensorRows (Word wordEncoding)
open RuntimeEOViewSupport (ZeroRow zeroRowEncoding tableEncoding)
open ComplexIsolation.RootSearchDriver (cross mem_cross)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

abbrev Table := List ZeroRow
abbrev Triple := ZeroRow × (ZeroRow × ZeroRow)
abbrev tripleTailEncoding := pairEncoding zeroRowEncoding zeroRowEncoding
abbrev tripleEncoding := pairEncoding zeroRowEncoding tripleTailEncoding
abbrev triplesEncoding := framedListEncoding tripleEncoding
abbrev Words := Word × (Word × Word)
abbrev wordsTailEncoding := pairEncoding wordEncoding wordEncoding
abbrev wordsEncoding := pairEncoding wordEncoding wordsTailEncoding
abbrev LookupInput := Table × Word
abbrev lookupEncoding := pairEncoding tableEncoding wordEncoding

def xorWord (r : Words) : Word := (List.range r.1.length).map
  (fun j => Bool.xor (Bool.xor (r.1.getD j false) (r.2.1.getD j false)) (r.2.2.getD j false))
def lookupZero (r : LookupInput) : Bool := r.1.any (fun p => decide (p.1=r.2) && p.2)
def domainBad (p : ZeroRow) : Bool := !p.2 && !decide (2*RuntimeSupportFlags.wordWeight p.1=p.1.length)
def triples (t : Table) : List Triple := cross t (cross t t)
def wordsOf (t : Triple) : Words := (t.1.1,t.2.1.1,t.2.2.1)
def zeroOf (t : Triple) : (Bool × Bool) × Bool := ((t.1.2,t.2.1.2),t.2.2.2)
def tripleBad (negative : Bool) (table : Table) (t : Triple) : Bool :=
  !t.1.2 && !t.2.1.2 && !t.2.2.2 && lookupZero (table,xorWord (wordsOf t)) &&
    RuntimeSupportFlags.sign negative (xorWord (wordsOf t))
def domainFailures (table : Table) := table.filter domainBad
def tripleFailures (negative : Bool) (table : Table) := (triples table).filter (tripleBad negative table)
abbrev Output := Table × (List Triple × List Triple)
abbrev outputEncoding := pairEncoding tableEncoding (pairEncoding triplesEncoding triplesEncoding)
def output (table : Table) : Output := (domainFailures table,tripleFailures true table,tripleFailures false table)

def xorExecutes : Executes wordsEncoding wordEncoding xorWord := by
  let r := RuntimeTensorRows.fst wordsEncoding encodingNatBool
  let j := RuntimeTensorRows.snd wordsEncoding encodingNatBool
  let x := r.comp (RuntimeTensorRows.fst wordEncoding wordsTailEncoding)
  let tail := r.comp (RuntimeTensorRows.snd wordEncoding wordsTailEncoding)
  let y := tail.comp (RuntimeTensorRows.fst wordEncoding wordEncoding)
  let z := tail.comp (RuntimeTensorRows.snd wordEncoding wordEncoding)
  let lookup {f : Words × ℕ → Word} (w : Executes (pairEncoding wordsEncoding encodingNatBool) wordEncoding f) :=
    (w.pair j).comp (RuntimeTensorRows.lookup encodingBoolBool false)
  let xor := Holant.LocalDrafts.Tractability.ProductMachine.Rewrite.boolPairComputes (fun p => Bool.xor p.1 p.2)
  let cell := (((lookup x).pair (lookup y)).comp (Executes.ofComputes xor)).pair (lookup z) |>.comp (Executes.ofComputes xor)
  let count := (RuntimeTensorRows.fst wordEncoding wordsTailEncoding).comp (RuntimeTensorRows.length encodingBoolBool)
  exact NegativeCertificateMachine.Lists.map wordsEncoding encodingNatBool encodingBoolBool
    (count.comp RationalInputMachine.Programs.range)
    (fun r j => Bool.xor (Bool.xor (r.1.getD j false) (r.2.1.getD j false)) (r.2.2.getD j false)) cell

def lookupComputes : Computes lookupEncoding encodingBoolBool lookupZero := by
  let test : Computes (pairEncoding wordEncoding zeroRowEncoding) encodingBoolBool
      (fun p => decide (p.2.1=p.1) && p.2.2) := by
    let w := Wiring.firstComputes wordEncoding zeroRowEncoding
    let p := Wiring.secondComputes wordEncoding zeroRowEncoding
    let key := p.andThen (Wiring.firstComputes wordEncoding encodingBoolBool)
    let z := p.andThen (Wiring.secondComputes wordEncoding encodingBoolBool)
    exact (pairComputes ((pairComputes key w).andThen (equalComputes wordEncoding)) z).andThen
      (Holant.LocalDrafts.Tractability.ProductMachine.Rewrite.boolPairComputes (fun q => q.1 && q.2))
  let swapped := pairComputes (Wiring.secondComputes tableEncoding wordEncoding)
    (Wiring.firstComputes tableEncoding wordEncoding)
  exact congrComputes (swapped.andThen ((mapListComputes wordEncoding zeroRowEncoding encodingBoolBool
    (fun w p => decide (p.1=w) && p.2) test).andThen ResidueCells.any))
      (fun r => by simp only [lookupZero,List.any_map,Function.comp_def,id_eq])

def domainBadExecutes : Executes zeroRowEncoding encodingBoolBool domainBad := by
  let w := RuntimeTensorRows.fst wordEncoding encodingBoolBool
  let z := RuntimeTensorRows.snd wordEncoding encodingBoolBool
  let weight := w.comp RuntimeSupportFlags.weightExecutes
  let double := (weight.pair weight).comp (Executes.ofComputes RationalInputMachine.Programs.add)
  let len := w.comp (RuntimeTensorRows.length encodingBoolBool)
  let central := (double.pair len).comp (Executes.ofComputes (equalComputes encodingNatBool))
  let raw := (z.pair central).comp (Executes.ofComputes
    (Holant.LocalDrafts.Tractability.ProductMachine.Rewrite.boolPairComputes (fun p => !p.1 && !p.2)))
  exact raw.congr (fun r => by simp only [domainBad,two_mul])

def wordsComputes : Computes tripleEncoding wordsEncoding wordsOf := by
  let a := Wiring.firstComputes zeroRowEncoding tripleTailEncoding
  let tail := Wiring.secondComputes zeroRowEncoding tripleTailEncoding
  let b := tail.andThen (Wiring.firstComputes zeroRowEncoding zeroRowEncoding)
  let c := tail.andThen (Wiring.secondComputes zeroRowEncoding zeroRowEncoding)
  exact pairComputes (a.andThen (Wiring.firstComputes wordEncoding encodingBoolBool))
    (pairComputes (b.andThen (Wiring.firstComputes wordEncoding encodingBoolBool))
      (c.andThen (Wiring.firstComputes wordEncoding encodingBoolBool)))

def nonzeroComputes : Computes tripleEncoding encodingBoolBool (fun t => !t.1.2 && !t.2.1.2 && !t.2.2.2) := by
  let a := (Wiring.firstComputes zeroRowEncoding tripleTailEncoding).andThen (Wiring.secondComputes wordEncoding encodingBoolBool)
  let tail := Wiring.secondComputes zeroRowEncoding tripleTailEncoding
  let b := (tail.andThen (Wiring.firstComputes zeroRowEncoding zeroRowEncoding)).andThen (Wiring.secondComputes wordEncoding encodingBoolBool)
  let c := (tail.andThen (Wiring.secondComputes zeroRowEncoding zeroRowEncoding)).andThen (Wiring.secondComputes wordEncoding encodingBoolBool)
  let eb := pairEncoding (pairEncoding encodingBoolBool encodingBoolBool) encodingBoolBool
  let op := FiniteRecode.computes eb encodingBoolBool
    (fun p : (Bool × Bool) × Bool => !p.1.1 && !p.1.2 && !p.2) 32
      (by rintro ⟨⟨a,b⟩,c⟩; cases a <;> cases b <;> cases c <;> decide)
  exact (pairComputes (pairComputes a b) c).andThen op

abbrev checkEncoding := pairEncoding (pairEncoding encodingBoolBool tableEncoding) tripleEncoding

def tripleBadExecutes : Executes checkEncoding encodingBoolBool (fun p => tripleBad p.1.1 p.1.2 p.2) := by
  let ctx := RuntimeTensorRows.fst (pairEncoding encodingBoolBool tableEncoding) tripleEncoding
  let t := RuntimeTensorRows.snd (pairEncoding encodingBoolBool tableEncoding) tripleEncoding
  let sign := ctx.comp (RuntimeTensorRows.fst encodingBoolBool tableEncoding)
  let table := ctx.comp (RuntimeTensorRows.snd encodingBoolBool tableEncoding)
  let word := (t.comp (Executes.ofComputes wordsComputes)).comp xorExecutes
  let z := (table.pair word).comp (Executes.ofComputes lookupComputes)
  let signTest := (sign.pair word).comp RuntimeSupportFlags.signExecutes
  let nz := t.comp (Executes.ofComputes nonzeroComputes)
  let and := Holant.LocalDrafts.Tractability.ProductMachine.Rewrite.boolPairComputes (fun p => p.1 && p.2)
  exact ((nz.pair z).comp (Executes.ofComputes and)).pair signTest |>.comp (Executes.ofComputes and)

/-- Generic physical filter with runtime context, not a supplied accepted list. -/
def filterExecutes {A B : Type} (ea : Encoding A Bool) (eb : Encoding B Bool)
    {xs : A → List B} {test : A → B → Bool} (list : Executes ea (framedListEncoding eb) xs)
    (check : Executes (pairEncoding ea eb) encodingBoolBool (fun p => test p.1 p.2)) :
    Executes ea (framedListEncoding eb) (fun a => (xs a).filter (test a)) := by
  let emit := RuntimeTensorRows.choose (pairEncoding ea eb) (framedListEncoding eb) check
    ((RuntimeTensorRows.snd ea eb).comp (Executes.ofComputes (NegativeCertificateMachine.Lists.singleton eb)))
    (RuntimeTensorRows.const (pairEncoding ea eb) (framedListEncoding eb) [])
  let raw := (NegativeCertificateMachine.Lists.map ea eb (framedListEncoding eb) list
    (fun a b => if test a b then [b] else []) emit).comp (Executes.ofComputes (WireLists.flatten eb))
  exact raw.congr (fun a => by
    rw [←List.flatMap_def]
    induction xs a with
    | nil => rfl
    | cons b bs ih =>
      simp only [List.flatMap_cons,List.filter_cons]
      cases h : test a b <;> simp [h,ih])

def triplesComputes : Computes tableEncoding triplesEncoding triples := by
  let t := identityComputes tableEncoding
  let inner := (pairComputes t t).andThen (ComplexIsolation.RootSearchDriver.crossComputes zeroRowEncoding zeroRowEncoding)
  exact (pairComputes t inner).andThen (ComplexIsolation.RootSearchDriver.crossComputes zeroRowEncoding tripleTailEncoding)

def domainExecutes : Executes tableEncoding tableEncoding domainFailures :=
  filterExecutes tableEncoding zeroRowEncoding (Executes.ofComputes (identityComputes tableEncoding))
    ((RuntimeTensorRows.snd tableEncoding zeroRowEncoding).comp domainBadExecutes)

def triplesExecutes (negative : Bool) : Executes tableEncoding triplesEncoding (tripleFailures negative) := by
  let c := RuntimeTensorRows.fst tableEncoding tripleEncoding
  let t := RuntimeTensorRows.snd tableEncoding tripleEncoding
  let b := RuntimeTensorRows.const (pairEncoding tableEncoding tripleEncoding) encodingBoolBool negative
  exact filterExecutes tableEncoding tripleEncoding (Executes.ofComputes triplesComputes)
    (((b.pair c).pair t).comp tripleBadExecutes)

def executes : Executes tableEncoding outputEncoding output :=
  domainExecutes.pair ((triplesExecutes true).pair (triplesExecutes false))

end
end Holant.LocalDrafts.RemoteWork.TractChainV1.RuntimeEOSupportCheck
