import Holant.Proofs.Recognition.RuntimeTensorReification

/-!
# Runtime sparse tensor equations

This finite programme reads width, arity, raw candidate metadata, and original
coefficient addresses. Every transformed entry, block slice, cleared tensor
row, inverse-pivot guard, and optional one-hot support row is constructed by
physical list/arithmetic programmes. The raw candidate is tape data supplied
by the catalogue stage; no typed partition proof, transformed RootCode, or
precompiled polynomial system is a machine input. This component alone does
not assemble the fixed basis equations or run RootCode witness search.
-/
namespace Holant.LocalDrafts.RemoteWork.TractChainV1.RuntimeTensorRows
open Turing Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing UniversalPairReduction.SmoothingCompiler
open Holant.LocalDrafts.MainChain.TransformRecognition
open Holant.LocalDrafts.EffectiveAlgebraic
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.Tractability.AffineMachine
open CommonFieldMachine (Executes)
open UniformTensorWitnessBranch (Metadata metadataEncoding natListEncoding)
open RationalSparseMachine (Poly)

abbrev Word := List Bool
abbrev wordEncoding := RationalTensorMachine.wordEncoding
abbrev tableEncoding := RationalTensorMachine.tableEncoding
abbrev metadataTailEncoding := pairEncoding natListEncoding wordEncoding
abbrev OffsetInput := List ℕ × ℕ
abbrev offsetEncoding := pairEncoding natListEncoding encodingNatBool
abbrev BlockInput := Metadata × ℕ
abbrev blockEncoding := pairEncoding metadataEncoding encodingNatBool
abbrev SliceInput := Word × (List ℕ × Word)
abbrev sliceTailEncoding := pairEncoding natListEncoding wordEncoding
abbrev sliceEncoding := pairEncoding wordEncoding sliceTailEncoding
abbrev SliceWordInput := Metadata × (ℕ × Word)
abbrev indexWordEncoding := pairEncoding encodingNatBool wordEncoding
abbrev sliceWordEncoding := pairEncoding metadataEncoding indexWordEncoding

-- Every lookup is total on raw packets; shape soundness uses validation.
def offset (p : OffsetInput) : ℕ := ((List.range p.2).map (fun i => p.1.getD i 0)).sum
def block (p : BlockInput) : List ℕ :=
  (List.range (p.1.1.getD p.2 0)).map (fun j => p.1.2.1.getD (offset (p.1.1,p.2)+j) 0)
def slice (p : SliceInput) : Word :=
  (List.range p.1.length).map (fun j =>
    if RuntimeTensorValidation.member j p.2.1 then p.2.2.getD j false else p.1.getD j false)
def sliceWord (p : SliceWordInput) : Word := slice (p.1.2.2,block (p.1,p.2.1),p.2.2)
def bitNat (b : Bool) : ℕ := if b then 1 else 0
def weight (p : List ℕ × Word) : ℕ := (p.1.map (fun j => bitNat (p.2.getD j false))).sum

def highWeight (k : ℕ) : Bool := !(decide (k=0) || decide (k=1))
theorem highWeight_correct (k : ℕ) : highWeight k=true ↔ 1<k := by
  simp [highWeight]
  omega

noncomputable section
variable {A B C : Type}

def fst (ea : Encoding A Bool) (eb : Encoding B Bool) :
    Executes (pairEncoding ea eb) ea Prod.fst := Executes.ofComputes (Wiring.firstComputes ea eb)
def snd (ea : Encoding A Bool) (eb : Encoding B Bool) :
    Executes (pairEncoding ea eb) eb Prod.snd := Executes.ofComputes (Wiring.secondComputes ea eb)
def const (ea : Encoding A Bool) (eb : Encoding B Bool) (b : B) : Executes ea eb (fun _ => b) :=
  Executes.ofComputes (constantComputes ea eb b)
def length (ea : Encoding A Bool) : Executes (framedListEncoding ea) encodingNatBool List.length :=
  Executes.ofComputes ((WireLists.lengthComputes ea).andThen UnaryBinary.computes)
def lookup (ea : Encoding A Bool) (a : A) := NegativeCertificateMachine.Lists.lookup ea a

def choose (ea : Encoding A Bool) (eb : Encoding B Bool)
    {test : A → Bool} {yes no : A → B} (t : Executes ea encodingBoolBool test)
    (y : Executes ea eb yes) (n : Executes ea eb no) :
    Executes ea eb (fun a => if test a then yes a else no a) := by
  let ys := (Wiring.secondComputes encodingBoolBool (pairEncoding eb eb)).andThen (Wiring.firstComputes eb eb)
  let ns := (Wiring.secondComputes encodingBoolBool (pairEncoding eb eb)).andThen (Wiring.secondComputes eb eb)
  exact (t.pair (y.pair n)).comp (Executes.ofComputes
    (ifComputes (Wiring.firstComputes encodingBoolBool (pairEncoding eb eb)) ys ns))

def offsetExecutes : Executes offsetEncoding encodingNatBool offset := by
  let p := fst offsetEncoding encodingNatBool
  let i := snd offsetEncoding encodingNatBool
  let xs := p.comp (fst natListEncoding encodingNatBool)
  let cell := (xs.pair i).comp (lookup encodingNatBool 0)
  exact (NegativeCertificateMachine.Lists.map offsetEncoding encodingNatBool encodingNatBool
    ((snd natListEncoding encodingNatBool).comp RationalInputMachine.Programs.range)
    (fun p i => p.1.getD i 0) cell).comp ProductAllocationMachine.sumExecutes

def blockExecutes : Executes blockEncoding natListEncoding block := by
  let m := fst metadataEncoding encodingNatBool
  let i := snd metadataEncoding encodingNatBool
  let sizes := m.comp (fst natListEncoding metadataTailEncoding)
  let ports := (m.comp (snd natListEncoding metadataTailEncoding)).comp (fst natListEncoding wordEncoding)
  let count := (sizes.pair i).comp (lookup encodingNatBool 0)
  let start := (sizes.pair i).comp offsetExecutes
  let ctx := fst blockEncoding encodingNatBool
  let j := snd blockEncoding encodingNatBool
  let address := ((ctx.comp start).pair j).comp (Executes.ofComputes RationalInputMachine.Programs.add)
  let cell := ((ctx.comp ports).pair address).comp (lookup encodingNatBool 0)
  exact NegativeCertificateMachine.Lists.map blockEncoding encodingNatBool encodingNatBool
    (count.comp RationalInputMachine.Programs.range)
    (fun p j => p.1.2.1.getD (offset (p.1.1,p.2)+j) 0) cell

def sliceExecutes : Executes sliceEncoding wordEncoding slice := by
  let pivot := fst wordEncoding sliceTailEncoding
  let rest := snd wordEncoding sliceTailEncoding
  let ports := rest.comp (fst natListEncoding wordEncoding)
  let x := rest.comp (snd natListEncoding wordEncoding)
  let ctx := fst sliceEncoding encodingNatBool
  let j := snd sliceEncoding encodingNatBool
  let test := (j.pair (ctx.comp ports)).comp (Executes.ofComputes RuntimeTensorValidation.memberComputes)
  let yes := ((ctx.comp x).pair j).comp (lookup encodingBoolBool false)
  let no := ((ctx.comp pivot).pair j).comp (lookup encodingBoolBool false)
  exact NegativeCertificateMachine.Lists.map sliceEncoding encodingNatBool encodingBoolBool
    ((pivot.comp (length encodingBoolBool)).comp RationalInputMachine.Programs.range)
    (fun p j => if RuntimeTensorValidation.member j p.2.1 then p.2.2.getD j false else p.1.getD j false)
    (choose _ _ test yes no)

def sliceWordExecutes : Executes sliceWordEncoding wordEncoding sliceWord := by
  let m := fst metadataEncoding indexWordEncoding
  let ix := snd metadataEncoding indexWordEncoding
  let i := ix.comp (fst encodingNatBool wordEncoding)
  let x := ix.comp (snd encodingNatBool wordEncoding)
  let pivot := (m.comp (snd natListEncoding metadataTailEncoding)).comp (snd natListEncoding wordEncoding)
  exact (pivot.pair (((m.pair i).comp blockExecutes).pair x)).comp sliceExecutes

def bitNatComputes : Computes encodingBoolBool encodingNatBool bitNat :=
  FiniteRecode.computes _ _ bitNat 1 (fun b => by cases b <;> decide)

def weightExecutes : Executes sliceTailEncoding encodingNatBool weight := by
  let p := fst sliceTailEncoding encodingNatBool
  let x := p.comp (snd natListEncoding wordEncoding)
  let j := snd sliceTailEncoding encodingNatBool
  let cell := ((x.pair j).comp (lookup encodingBoolBool false)).comp (Executes.ofComputes bitNatComputes)
  exact (NegativeCertificateMachine.Lists.map sliceTailEncoding encodingNatBool encodingNatBool
    (fst natListEncoding wordEncoding) (fun p j => bitNat (p.2.getD j false)) cell).comp
      ProductAllocationMachine.sumExecutes

def highWeightComputes : Computes encodingNatBool encodingBoolBool highWeight := by
  let eq (n : ℕ) := (pairComputes (identityComputes encodingNatBool)
    (constantComputes encodingNatBool encodingNatBool n)).andThen (equalComputes encodingNatBool)
  let op := Holant.LocalDrafts.Tractability.ProductMachine.Rewrite.boolPairComputes
    (fun p => !(p.1 || p.2))
  exact (pairComputes (eq 0) (eq 1)).andThen op
end

abbrev Input := ℕ × (ℕ × (Metadata × List RationalTensorMachine.Row))
abbrev dataEncoding := pairEncoding metadataEncoding tableEncoding
abbrev tailEncoding := pairEncoding encodingNatBool dataEncoding
abbrev encoding := pairEncoding encodingNatBool tailEncoding
abbrev wordInputEncoding := pairEncoding encoding wordEncoding
abbrev supportEncoding := pairEncoding encoding indexWordEncoding

def count (r : Input) : ℕ := r.2.2.1.1.length
def pivot (r : Input) : Word := r.2.2.1.2.2
def value (r : Input) (x : Word) : Poly := RationalTensorMachine.vertex (r.1,x,r.2.2.2)
def sliceValue (r : Input) (i : ℕ) (x : Word) : Poly := value r (sliceWord (r.2.2.1,i,x))
def row (r : Input) (x : Word) : Poly :=
  RationalSparseMachine.sub
    (RationalSparseMachine.mul (value r (pivot r))
      (RationalSparseMachine.product r.1 ((List.range (count r)).map (fun i => sliceValue r i x))))
    (RationalSparseMachine.mul (value r x)
      (RationalSparseMachine.product r.1 ((List.range (count r)).map (fun _ => value r (pivot r)))))
def guard (r : Input) : Poly := RationalSparseMachine.sub
  (RationalSparseMachine.mul (value r (pivot r)) (RationalSparseMachine.variable r.1 5))
  (RationalSparseMachine.one r.1)
def support (r : Input) (p : ℕ × Word) : Poly :=
  if highWeight (weight (block (r.2.2.1,p.1),p.2)) then sliceValue r p.1 p.2 else []
def supportAt (r : Input) (x : Word) : List Poly :=
  (List.range (count r)).map (fun i => support r (i,x))
/-- The identically-zero table is handled by a distinct branch without a
nonzero-pivot guard. -/
def zeroRows (r : Input) : List Poly := (RationalTableMachine.words r.2.1).map (value r)
def rows (oneHot : Bool) (r : Input) : List Poly :=
  guard r :: (RationalTableMachine.words r.2.1).flatMap
    (fun x => row r x :: if oneHot then supportAt r x else [])

noncomputable section

def width := fst encodingNatBool tailEncoding
def tail := snd encodingNatBool tailEncoding
def arity := tail.comp (fst encodingNatBool dataEncoding)
def data := tail.comp (snd encodingNatBool dataEncoding)
def metadata := data.comp (fst metadataEncoding tableEncoding)
def table := data.comp (snd metadataEncoding tableEncoding)
def pivotExecutes : Executes encoding wordEncoding pivot :=
  (metadata.comp (snd natListEncoding metadataTailEncoding)).comp (snd natListEncoding wordEncoding)
def countExecutes : Executes encoding encodingNatBool count :=
  (metadata.comp (fst natListEncoding metadataTailEncoding)).comp (length encodingNatBool)
def valueExecutes : Executes wordInputEncoding RationalSparseMachine.encoding (fun p => value p.1 p.2) := by
  let r := fst encoding wordEncoding
  let x := snd encoding wordEncoding
  exact ((r.comp width).pair (x.pair (r.comp table))).comp RationalTensorMachine.vertexExecutes

def zeroRowsExecutes : Executes encoding RationalSparseMachine.familyEncoding zeroRows :=
  NegativeCertificateMachine.Lists.map encoding wordEncoding RationalSparseMachine.encoding
    (arity.comp RationalTableMachine.wordsExecutes) value valueExecutes

def pivotValueExecutes : Executes encoding RationalSparseMachine.encoding (fun r => value r (pivot r)) :=
  ((Executes.ofComputes (identityComputes encoding)).pair pivotExecutes).comp valueExecutes

def sliceValueExecutes : Executes supportEncoding RationalSparseMachine.encoding
    (fun p => sliceValue p.1 p.2.1 p.2.2) := by
  let r := fst encoding indexWordEncoding
  let ix := snd encoding indexWordEncoding
  let x := ((r.comp metadata).pair ix).comp sliceWordExecutes
  exact (r.pair x).comp valueExecutes

def rowExecutes : Executes wordInputEncoding RationalSparseMachine.encoding (fun p => row p.1 p.2) := by
  let r := fst encoding wordEncoding
  let x := snd encoding wordEncoding
  let ctx := fst wordInputEncoding encodingNatBool
  let i := snd wordInputEncoding encodingNatBool
  let cell := ((ctx.comp r).pair (i.pair (ctx.comp x))).comp sliceValueExecutes
  let indices := (r.comp countExecutes).comp RationalInputMachine.Programs.range
  let slices := NegativeCertificateMachine.Lists.map wordInputEncoding encodingNatBool RationalSparseMachine.encoding
    indices (fun p i => sliceValue p.1 i p.2) cell
  let prod := ((r.comp width).pair slices).comp RationalSparseMachine.productExecutes
  let lhs := ((r.comp pivotValueExecutes).pair prod).comp RationalSparseMachine.mulExecutes
  let repeated := NegativeCertificateMachine.Lists.map wordInputEncoding encodingNatBool RationalSparseMachine.encoding
    indices (fun p _ => value p.1 (pivot p.1)) ((ctx.comp r).comp pivotValueExecutes)
  let power := ((r.comp width).pair repeated).comp RationalSparseMachine.productExecutes
  let rhs := (valueExecutes.pair power).comp RationalSparseMachine.mulExecutes
  exact (lhs.pair rhs).comp (Executes.ofComputes RationalSparseMachine.subComputes)

def guardExecutes : Executes encoding RationalSparseMachine.encoding guard := by
  let inverse := (width.pair (const encoding encodingNatBool 5)).comp RationalSparseMachine.variableExecutes
  let lhs := (pivotValueExecutes.pair inverse).comp RationalSparseMachine.mulExecutes
  exact (lhs.pair (width.comp RationalSparseMachine.oneExecutes)).comp
    (Executes.ofComputes RationalSparseMachine.subComputes)

def supportExecutes : Executes supportEncoding RationalSparseMachine.encoding
    (fun p => support p.1 p.2) := by
  let r := fst encoding indexWordEncoding
  let ix := snd encoding indexWordEncoding
  let i := ix.comp (fst encodingNatBool wordEncoding)
  let x := ix.comp (snd encodingNatBool wordEncoding)
  let ports := ((r.comp metadata).pair i).comp blockExecutes
  let test := ((ports.pair x).comp weightExecutes).comp (Executes.ofComputes highWeightComputes)
  exact choose _ _ test sliceValueExecutes (const supportEncoding RationalSparseMachine.encoding [])

def supportAtExecutes : Executes wordInputEncoding RationalSparseMachine.familyEncoding
    (fun p => supportAt p.1 p.2) := by
  let r := fst encoding wordEncoding
  let x := snd encoding wordEncoding
  let ctx := fst wordInputEncoding encodingNatBool
  let i := snd wordInputEncoding encodingNatBool
  let cell := ((ctx.comp r).pair (i.pair (ctx.comp x))).comp supportExecutes
  exact NegativeCertificateMachine.Lists.map wordInputEncoding encodingNatBool RationalSparseMachine.encoding
    ((r.comp countExecutes).comp RationalInputMachine.Programs.range)
    (fun p i => support p.1 (i,p.2)) cell

abbrev modeEncoding := pairEncoding encodingBoolBool encoding
abbrev modeWordEncoding := pairEncoding modeEncoding wordEncoding

def rowsExecutes : Executes modeEncoding RationalSparseMachine.familyEncoding (fun p => rows p.1 p.2) := by
  let mode := fst encodingBoolBool encoding
  let r := snd encodingBoolBool encoding
  let ctx := fst modeEncoding wordEncoding
  let x := snd modeEncoding wordEncoding
  let rx := (ctx.comp r).pair x
  let optional := choose modeWordEncoding RationalSparseMachine.familyEncoding
    (ctx.comp mode) (rx.comp supportAtExecutes) (const modeWordEncoding RationalSparseMachine.familyEncoding [])
  let singleton := (rx.comp rowExecutes).comp (Executes.ofComputes
    (NegativeCertificateMachine.Lists.singleton RationalSparseMachine.encoding))
  let cell := (singleton.pair optional).comp (Executes.ofComputes
    (WireLists.append RationalSparseMachine.encoding))
  let body := (NegativeCertificateMachine.Lists.map modeEncoding wordEncoding RationalSparseMachine.familyEncoding
    ((r.comp arity).comp RationalTableMachine.wordsExecutes)
    (fun p x => row p.2 x :: if p.1 then supportAt p.2 x else []) cell).comp
      (Executes.ofComputes (WireLists.flatten RationalSparseMachine.encoding))
  let header := (r.comp guardExecutes).comp (Executes.ofComputes
    (NegativeCertificateMachine.Lists.singleton RationalSparseMachine.encoding))
  exact ((header.pair body).comp (Executes.ofComputes
    (WireLists.append RationalSparseMachine.encoding))).congr
      (fun _ => rfl)

def source_outputs (oneHot : Bool) (r : Input) : TM2OutputsInTime rowsExecutes.machine.computer
    (modeEncoding.encode (oneHot,r))
    (some (RationalSparseMachine.familyEncoding.encode (rows oneHot r))) (rowsExecutes.cost (oneHot,r)) :=
  rowsExecutes.outputs (oneHot,r)

theorem primitive_bound (oneHot : Bool) (r : Input) :
    primitiveCost rowsExecutes.machine (rowsExecutes.outputs (oneHot,r)).steps
      (some (initList rowsExecutes.machine.computer (modeEncoding.encode (oneHot,r)))) ≤
        rowsExecutes.cost (oneHot,r)*rowsExecutes.machine.primitiveBudget :=
  rowsExecutes.primitive_bound (oneHot,r)

/-- Storage of every prefix of this same emitted-row programme. -/
theorem prefix_bits (oneHot : Bool) (r : Input) (k : ℕ)
    (hk : k ≤ (rowsExecutes.outputs (oneHot,r)).steps)
    (c : rowsExecutes.machine.Config)
    (hc : (fun p => p.bind rowsExecutes.machine.computer.step)^[k]
      (some (initList rowsExecutes.machine.computer (modeEncoding.encode (oneHot,r)))) = some c) :
    stackSize c.stk ≤ (modeEncoding.encode (oneHot,r)).length +
      rowsExecutes.cost (oneHot,r)*rowsExecutes.machine.primitiveBudget := by
  have h := rowsExecutes.machine.run_size_le
    (initList rowsExecutes.machine.computer (modeEncoding.encode (oneHot,r))) c k hc
  rw [Machine.size_init] at h
  exact h.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _
    (hk.trans (rowsExecutes.outputs (oneHot,r)).steps_le_m)) _)

end
end Holant.LocalDrafts.RemoteWork.TractChainV1.RuntimeTensorRows
