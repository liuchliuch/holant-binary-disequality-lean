import Holant.Proofs.Recognition.RuntimeSupportTable
import Holant.Proofs.Recognition.UniformKSupport

/-! Actual finite support/layer scans of the retained runtime zero-search table.
No algebraic search is repeated by this finishing stage. The comparisons and
folds are physical programmes on stored words/options, uniform in every arity. -/
namespace Holant.LocalDrafts.RemoteWork.TractChainV1.RuntimeSupportFlags
open Turing Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing UniversalPairReduction.SmoothingCompiler
open Holant.LocalDrafts.MainChain.TransformRecognition
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.Tractability.AffineMachine
open CommonFieldMachine (Executes)
open RuntimeTensorRows (Word wordEncoding)
open RuntimeSupportTable (Packet packetEncoding LabelPacket labelPacketEncoding labelResultEncoding)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

def wordWeight (w : Word) : ℕ := (w.map RuntimeTensorRows.bitNat).sum
def le (p : ℕ × ℕ) : Bool := RuntimeTensorValidation.member p.1 (List.range (p.2+1))
def sign (negative : Bool) (w : Word) : Bool :=
  if negative then le (2*wordWeight w,w.length) else le (w.length,2*wordWeight w)
def cell (negative : Bool) (p : Packet) : Bool := sign negative p.1 || p.2.isSome
def side (negative : Bool) (r : List LabelPacket) : Bool := r.all (fun p => p.2.all (cell negative))
def layerCell (k : ℕ) (p : Packet) : Bool := decide (wordWeight p.1=k) || p.2.isSome
def layer (k : ℕ) (r : List Packet) : Bool := r.all (layerCell k)

theorem wordWeight_source {n : ℕ} (x : Fin n → Bool) : wordWeight (List.ofFn x)=Holant.weight x := by
  simp only [wordWeight,List.map_ofFn,List.sum_ofFn,Function.comp_def,RuntimeTensorRows.bitNat,Holant.weight]
theorem le_correct (a b : ℕ) : le (a,b)=true ↔ a≤b := by
  simp [le,RuntimeTensorValidation.member_correct]
theorem sign_correct (negative : Bool) {n : ℕ} (x : Fin n → Bool) :
    sign negative (List.ofFn x)=true ↔ UniformKSupport.signHolds negative x := by
  cases negative <;> simp only [sign,Bool.false_eq_true,ite_false,ite_true,wordWeight_source,
    List.length_ofFn,le_correct,UniformKSupport.signHolds,Holant.charge] <;> omega

abbrev natPairEncoding := pairEncoding encodingNatBool encodingNatBool
abbrev signEncoding := pairEncoding encodingBoolBool wordEncoding
abbrev cellEncoding := pairEncoding encodingBoolBool packetEncoding
abbrev sideEncoding := pairEncoding encodingBoolBool RuntimeSupportTable.resultEncoding
abbrev layerCellEncoding := pairEncoding encodingNatBool packetEncoding
abbrev layerEncoding := pairEncoding encodingNatBool labelResultEncoding

def weightExecutes : Executes wordEncoding encodingNatBool wordWeight :=
  (Executes.ofComputes (WireLists.mapComputes encodingBoolBool encodingNatBool RuntimeTensorRows.bitNat
    RuntimeTensorRows.bitNatComputes)).comp ProductAllocationMachine.sumExecutes

def leExecutes : Executes natPairEncoding encodingBoolBool le := by
  let a := RuntimeTensorRows.fst encodingNatBool encodingNatBool
  let b := RuntimeTensorRows.snd encodingNatBool encodingNatBool
  let range := (b.comp (Executes.ofComputes RationalInputMachine.Programs.successor)).comp RationalInputMachine.Programs.range
  exact (a.pair range).comp (Executes.ofComputes RuntimeTensorValidation.memberComputes)

def signExecutes : Executes signEncoding encodingBoolBool (fun p => sign p.1 p.2) := by
  let b := RuntimeTensorRows.fst encodingBoolBool wordEncoding
  let w := RuntimeTensorRows.snd encodingBoolBool wordEncoding
  let length := w.comp (RuntimeTensorRows.length encodingBoolBool)
  let weight := w.comp weightExecutes
  let double := (weight.pair weight).comp (Executes.ofComputes RationalInputMachine.Programs.add)
  have hd : ∀p : Bool × Word,wordWeight p.2+wordWeight p.2=2*wordWeight p.2 := by intro p; omega
  let d : Executes signEncoding encodingNatBool (fun p => 2*wordWeight p.2) :=
    Executes.recode double id (fun _ => rfl) (fun p => congrArg encodingNatBool.encode (hd p))
  exact RuntimeTensorRows.choose _ _ b ((d.pair length).comp leExecutes) ((length.pair d).comp leExecutes)

def cellExecutes : Executes cellEncoding encodingBoolBool (fun p => cell p.1 p.2) := by
  let b := RuntimeTensorRows.fst encodingBoolBool packetEncoding
  let p := RuntimeTensorRows.snd encodingBoolBool packetEncoding
  let w := p.comp (RuntimeTensorRows.fst wordEncoding Holant.LocalDrafts.EffectiveAlgebraic.WitnessOutput.resultEncoding)
  let present := p.comp (Executes.ofComputes ((Wiring.secondComputes wordEncoding
    Holant.LocalDrafts.EffectiveAlgebraic.WitnessOutput.resultEncoding).andThen UniformTractXDecision.presence))
  exact (((b.pair w).comp signExecutes).pair present).comp
    (Executes.ofComputes (Holant.LocalDrafts.Tractability.ProductMachine.Rewrite.boolPairComputes (fun q => q.1 || q.2)))

def labelSideExecutes : Executes (pairEncoding encodingBoolBool labelResultEncoding) encodingBoolBool
    (fun p => p.2.all (cell p.1)) := by
  let ec := pairEncoding encodingBoolBool labelResultEncoding
  let c := RuntimeTensorRows.fst ec packetEncoding
  let p := RuntimeTensorRows.snd ec packetEncoding
  let b := c.comp (RuntimeTensorRows.fst encodingBoolBool labelResultEncoding)
  let raw := (NegativeCertificateMachine.Lists.map ec packetEncoding encodingBoolBool
    (RuntimeTensorRows.snd encodingBoolBool labelResultEncoding) (fun r p => cell r.1 p)
      ((b.pair p).comp cellExecutes)).comp (Executes.ofComputes ResidueCells.all)
  exact Executes.recode raw id (fun _ => rfl)
    (fun p => congrArg encodingBoolBool.encode (by simp only [List.all_map,Function.comp_def,id_eq]))

def sideExecutes : Executes sideEncoding encodingBoolBool (fun p => side p.1 p.2) := by
  let c := RuntimeTensorRows.fst sideEncoding labelPacketEncoding
  let p := RuntimeTensorRows.snd sideEncoding labelPacketEncoding
  let b := c.comp (RuntimeTensorRows.fst encodingBoolBool RuntimeSupportTable.resultEncoding)
  let ps := p.comp (RuntimeTensorRows.snd encodingNatBool labelResultEncoding)
  let raw := (NegativeCertificateMachine.Lists.map sideEncoding labelPacketEncoding encodingBoolBool
    (RuntimeTensorRows.snd encodingBoolBool RuntimeSupportTable.resultEncoding)
    (fun r p => p.2.all (cell r.1)) ((b.pair ps).comp labelSideExecutes)).comp
      (Executes.ofComputes ResidueCells.all)
  exact Executes.recode raw id (fun _ => rfl)
    (fun p => congrArg encodingBoolBool.encode (by simp only [side,List.all_map,Function.comp_def,id_eq]))


def layerCellExecutes : Executes layerCellEncoding encodingBoolBool (fun p => layerCell p.1 p.2) := by
  let k := RuntimeTensorRows.fst encodingNatBool packetEncoding
  let p := RuntimeTensorRows.snd encodingNatBool packetEncoding
  let w := (p.comp (RuntimeTensorRows.fst wordEncoding Holant.LocalDrafts.EffectiveAlgebraic.WitnessOutput.resultEncoding)).comp weightExecutes
  let equal := (w.pair k).comp (Executes.ofComputes (equalComputes encodingNatBool))
  let present := p.comp (Executes.ofComputes ((Wiring.secondComputes wordEncoding
    Holant.LocalDrafts.EffectiveAlgebraic.WitnessOutput.resultEncoding).andThen UniformTractXDecision.presence))
  exact (equal.pair present).comp (Executes.ofComputes
    (Holant.LocalDrafts.Tractability.ProductMachine.Rewrite.boolPairComputes (fun q => q.1 || q.2)))

def layerExecutes : Executes layerEncoding encodingBoolBool (fun p => layer p.1 p.2) := by
  let c := RuntimeTensorRows.fst layerEncoding packetEncoding
  let p := RuntimeTensorRows.snd layerEncoding packetEncoding
  let k := c.comp (RuntimeTensorRows.fst encodingNatBool labelResultEncoding)
  let raw := (NegativeCertificateMachine.Lists.map layerEncoding packetEncoding encodingBoolBool
    (RuntimeTensorRows.snd encodingNatBool labelResultEncoding) (fun r p => layerCell r.1 p)
      ((k.pair p).comp layerCellExecutes)).comp (Executes.ofComputes ResidueCells.all)
  exact raw.congr (fun p => by simp only [layer,List.all_map,Function.comp_def,id_eq])

theorem cell_correct (negative : Bool) (d : RuntimeSupportTable.LabelData)
    (x : Fin (d.1.arity d.2) → Bool) :
    cell negative (RuntimeSupportTable.packet d (List.ofFn x))=true ↔
      sourceKBasis.symm.action (d.1.G d.2) x≠0 → UniformKSupport.signHolds negative x := by
  change (sign negative (List.ofFn x) || (RuntimeSupportTable.entryOutput d (List.ofFn x)).isSome)=true ↔ _
  rw [Bool.or_eq_true,sign_correct,RuntimeSupportTable.source_zero_correct]
  tauto

theorem layerCell_correct (k : ℕ) (d : RuntimeSupportTable.LabelData)
    (x : Fin (d.1.arity d.2) → Bool) :
    layerCell k (RuntimeSupportTable.packet d (List.ofFn x))=true ↔
      Holant.weight x≠k → sourceKBasis.symm.action (d.1.G d.2) x=0 := by
  change (decide (wordWeight (List.ofFn x)=k) || (RuntimeSupportTable.entryOutput d (List.ofFn x)).isSome)=true ↔ _
  rw [Bool.or_eq_true,wordWeight_source,decide_eq_true_eq,RuntimeSupportTable.source_zero_correct]
  tauto

theorem label_layer_correct (k : ℕ) (d : RuntimeSupportTable.LabelData) :
    layer k (RuntimeSupportTable.labelOutput d)=true ↔
      Signature.SingleLayer (sourceKBasis.symm.action (d.1.G d.2)) k := by
  simp only [layer,RuntimeSupportTable.labelOutput,RuntimeSupportTable.items,RationalTableMachine.words_eq,
    List.all_map,List.all_eq_true,Function.comp_def,SparseTransform.mem_allWords,forall_true_left,layerCell_correct]
  rfl

theorem side_correct (negative : Bool) (d : RuntimeSupportTable.Data) :
    side negative (RuntimeSupportTable.output d)=true ↔
      ∀i x,sourceKBasis.symm.action (d.G i) x≠0 → UniformKSupport.signHolds negative x := by
  constructor
  · intro h i x
    have hl := List.all_eq_true.mp h (i.val,RuntimeSupportTable.labelOutput ⟨d,i⟩)
      (RuntimeSupportTable.retained d i x).1
    have hc := List.all_eq_true.mp hl (List.ofFn x,RuntimeSupportTable.entryOutput ⟨d,i⟩ (List.ofFn x))
      (RuntimeSupportTable.retained d i x).2
    exact (cell_correct negative ⟨d,i⟩ x).mp hc
  · intro h
    apply List.all_eq_true.mpr
    intro lp hlp
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hlp
    have hlt : j<d.count := List.mem_range.mp hj
    simp only [RuntimeSupportTable.atLabelOutput,dif_pos hlt]
    apply List.all_eq_true.mpr
    intro p hp
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hp
    obtain ⟨x,rfl⟩ := RuntimeSupportTable.word_exists ⟨d,⟨j,hlt⟩⟩ w hw
    exact (cell_correct negative ⟨d,⟨j,hlt⟩⟩ x).mpr (h ⟨j,hlt⟩ x)

abbrev Summary := Bool × Bool
abbrev summaryEncoding := pairEncoding encodingBoolBool encodingBoolBool
abbrev Output := Summary × List LabelPacket
abbrev outputEncoding := pairEncoding summaryEncoding RuntimeSupportTable.resultEncoding

def summary (r : List LabelPacket) : Summary := (side false r,side true r)
def finish (r : List LabelPacket) : Output := (summary r,r)
def summaryExecutes : Executes RuntimeSupportTable.resultEncoding summaryEncoding summary := by
  let r := Executes.ofComputes (identityComputes RuntimeSupportTable.resultEncoding)
  let b (v : Bool) := Executes.ofComputes
    (constantComputes RuntimeSupportTable.resultEncoding encodingBoolBool v)
  exact ((b false |>.pair r).comp sideExecutes).pair ((b true |>.pair r).comp sideExecutes)

def finishExecutes : Executes RuntimeSupportTable.resultEncoding outputEncoding finish :=
  summaryExecutes.pair (Executes.ofComputes (identityComputes RuntimeSupportTable.resultEncoding))

def output (d : RuntimeSupportTable.Data) : Output := finish (RuntimeSupportTable.output d)
def executes : PhysicalFolds.Runs OriginalFamilyPackingMachine.encoding outputEncoding RuntimeSupportTable.original output :=
  RuntimeSupportTable.executes.comp (RuntimeTensorEnumeration.ofExecutes finishExecutes RuntimeSupportTable.output)

theorem positive_correct (d : RuntimeSupportTable.Data) : (output d).1.1=true ↔
    ∀i x,sourceKBasis.symm.action (d.G i) x≠0 → 0≤Holant.charge x :=
  side_correct false d

theorem negative_correct (d : RuntimeSupportTable.Data) : (output d).1.2=true ↔
    ∀i x,sourceKBasis.symm.action (d.G i) x≠0 → Holant.charge x≤0 :=
  side_correct true d

/-- The finishing programme consumes only the stored support table. -/
theorem finishing_control : executes.machine=RuntimeSupportTable.executes.machine.compose finishExecutes.machine := rfl


def source_outputs (d : RuntimeSupportTable.Data) : TM2OutputsInTime executes.machine.computer
    (OriginalFamilyPackingMachine.encoding.encode (RuntimeSupportTable.original d))
    (some (outputEncoding.encode (output d))) (executes.cost d) := executes.outputs d

theorem resources (d : RuntimeSupportTable.Data) :
    primitiveCost executes.machine (executes.outputs d).steps
      (some (initList executes.machine.computer (OriginalFamilyPackingMachine.encoding.encode (RuntimeSupportTable.original d)))) ≤
      executes.cost d*executes.machine.primitiveBudget ∧
    ∀k,k≤(executes.outputs d).steps → ∀cfg : executes.machine.Config,
      (fun st => st.bind executes.machine.computer.step)^[k]
        (some (initList executes.machine.computer (OriginalFamilyPackingMachine.encoding.encode (RuntimeSupportTable.original d))))=some cfg →
      stackSize cfg.stk ≤ (OriginalFamilyPackingMachine.encoding.encode (RuntimeSupportTable.original d)).length+
        executes.cost d*executes.machine.primitiveBudget := by
  constructor
  · exact (primitiveCost_le _ _ _).trans (Nat.mul_le_mul_right _ (executes.outputs d).steps_le_m)
  · intro k hk cfg hc
    have h := executes.machine.run_size_le
      (initList executes.machine.computer (OriginalFamilyPackingMachine.encoding.encode (RuntimeSupportTable.original d))) cfg k hc
    rw [Machine.size_init] at h
    exact h.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ (hk.trans (executes.outputs d).steps_le_m)) _)

end
end Holant.LocalDrafts.RemoteWork.TractChainV1.RuntimeSupportFlags
