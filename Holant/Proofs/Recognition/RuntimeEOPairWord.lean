import Holant.Proofs.Recognition.RuntimeEOPairings

/-! Physical expansion of an oriented-pairing assignment. Only raw metadata
and a compressed Boolean word are read. Both incidences of each pair are looked
up in the stored forward port table; no inverse equivalence is machine input.
The source theorem covers every generated accepted pairing packet. -/
namespace Holant.LocalDrafts.RemoteWork.TractChainV1.RuntimeEOPairWord
open Turing Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing UniversalPairReduction.SmoothingCompiler
open Holant.LocalDrafts.MainChain.TransformRecognition
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.EffectiveAlgebraic
open Holant.LocalDrafts.Tractability.AffineMachine
open CommonFieldMachine (Executes)
open RuntimeTensorRows (Word wordEncoding)
open UniformTensorWitnessBranch (Metadata metadataEncoding natListEncoding)
open RuntimeEOPairings
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

abbrev Input := Metadata × Word
abbrev encoding := pairEncoding metadataEncoding wordEncoding
abbrev CellInput := Input × (ℕ × ℕ)
abbrev indexEncoding := pairEncoding encodingNatBool encodingNatBool
abbrev cellEncoding := pairEncoding encoding indexEncoding
abbrev wordCellEncoding := pairEncoding encoding encodingNatBool

def component (r : Input) (j i : ℕ) : Bool :=
  (decide (j=(RuntimeTensorRows.block (r.1,i)).getD 0 0) && r.2.getD i false) ||
  (decide (j=(RuntimeTensorRows.block (r.1,i)).getD 1 0) && !(r.2.getD i false))
def bit (r : Input) (j : ℕ) : Bool := (List.range r.1.1.length).any (component r j)
def word (r : Input) : Word := (List.range r.1.2.2.length).map (bit r)

def componentExecutes : Executes cellEncoding encodingBoolBool (fun p => component p.1 p.2.1 p.2.2) := by
  let r := RuntimeTensorRows.fst encoding indexEncoding
  let ji := RuntimeTensorRows.snd encoding indexEncoding
  let j := ji.comp (RuntimeTensorRows.fst encodingNatBool encodingNatBool)
  let i := ji.comp (RuntimeTensorRows.snd encodingNatBool encodingNatBool)
  let m := r.comp (RuntimeTensorRows.fst metadataEncoding wordEncoding)
  let w := r.comp (RuntimeTensorRows.snd metadataEncoding wordEncoding)
  let block := (m.pair i).comp RuntimeTensorRows.blockExecutes
  let entryAt (k : ℕ) := (block.pair (RuntimeTensorRows.const cellEncoding encodingNatBool k)).comp
    (RuntimeTensorRows.lookup encodingNatBool 0)
  let eq (k : ℕ) := (j.pair (entryAt k)).comp (Executes.ofComputes (equalComputes encodingNatBool))
  let z := (w.pair i).comp (RuntimeTensorRows.lookup encodingBoolBool false)
  let eb := pairEncoding (pairEncoding encodingBoolBool encodingBoolBool) encodingBoolBool
  let comb := FiniteRecode.computes eb encodingBoolBool
    (fun p : (Bool × Bool) × Bool => (p.1.1 && p.2) || (p.1.2 && !p.2)) 32
    (by rintro ⟨⟨a,b⟩,c⟩; cases a <;> cases b <;> cases c <;> decide)
  exact (((eq 0).pair (eq 1)).pair z).comp (Executes.ofComputes comb)

def bitExecutes : Executes wordCellEncoding encodingBoolBool (fun p => bit p.1 p.2) := by
  let r := RuntimeTensorRows.fst encoding encodingNatBool
  let j := RuntimeTensorRows.snd encoding encodingNatBool
  let count := ((r.comp (RuntimeTensorRows.fst metadataEncoding wordEncoding)).comp
    (RuntimeTensorRows.fst natListEncoding RuntimeTensorRows.metadataTailEncoding)).comp
      (RuntimeTensorRows.length encodingNatBool)
  let c := RuntimeTensorRows.fst wordCellEncoding encodingNatBool
  let i := RuntimeTensorRows.snd wordCellEncoding encodingNatBool
  let cell := ((c.comp r).pair ((c.comp j).pair i)).comp componentExecutes
  let raw := (NegativeCertificateMachine.Lists.map wordCellEncoding encodingNatBool encodingBoolBool
    (count.comp RationalInputMachine.Programs.range) (fun p i => component p.1 p.2 i) cell).comp
      (Executes.ofComputes ResidueCells.any)
  exact raw.congr (fun p => by simp only [bit,List.any_map,Function.comp_def,id_eq])

def executes : Executes encoding wordEncoding word := by
  let m := RuntimeTensorRows.fst metadataEncoding wordEncoding
  let pivot := (m.comp (RuntimeTensorRows.snd natListEncoding RuntimeTensorRows.metadataTailEncoding)).comp
    (RuntimeTensorRows.snd natListEncoding wordEncoding)
  let n := pivot.comp (RuntimeTensorRows.length encodingBoolBool)
  exact NegativeCertificateMachine.Lists.map encoding encodingNatBool encodingBoolBool
    (n.comp RationalInputMachine.Programs.range) bit bitExecutes

variable {n : ℕ} (m : Metadata) (hg : m∈RuntimeTensorCatalogue.catalogue n) (hv : valid n m=true)
local notation "p" => pairing m hg hv

theorem block_port (i : Fin (p).count) (b : Bool) :
    (RuntimeTensorRows.block (m,i.val)).getD (boolFin b).val 0=((p).ports (i,b)).val := by
  have h := ((valid_correct n m).mp hv).1
  have hs := ((valid_correct n m).mp hv).2 i
  rw [RuntimeTensorRowsSoundness.block_ports m hg false h]
  let k : Fin (RuntimeTensorReification.arity m i) := Fin.cast hs.symm (boolFin b)
  exact PositiveCertificateMachine.getD_ofFn
    (fun j : Fin (RuntimeTensorReification.arity m i) =>
      (RuntimeTensorReification.blockPorts m hg false h ⟨i,j⟩).val) k 0

theorem port_eq (a i : Fin (p).count) (b c : Bool) :
    ((p).ports (a,b)).val=((p).ports (i,c)).val ↔ a=i ∧ b=c := by
  constructor
  · intro h
    exact Prod.mk.inj ((p).ports.injective (Fin.ext h))
  · rintro ⟨rfl,rfl⟩
    rfl

theorem component_source (z : Fin (p).count → Bool) (a i : Fin (p).count) (b : Bool) :
    component (m,List.ofFn z) ((p).ports (a,b)).val i.val =
      if a=i then (if b then !(z a) else z a) else false := by
  unfold component
  have h0 := block_port m hg hv i false
  have h1 := block_port m hg hv i true
  change (RuntimeTensorRows.block (m,i.val)).getD 0 0=_ at h0
  change (RuntimeTensorRows.block (m,i.val)).getD 1 0=_ at h1
  rw [h0,h1,PositiveCertificateMachine.getD_ofFn]
  have he0 := port_eq m hg hv a i b false
  have he1 := port_eq m hg hv a i b true
  by_cases ha : a=i
  · subst i
    cases b <;> simp [he0,he1]
  · have hn0 : ((p).ports (a,b)).val≠((p).ports (i,false)).val := fun h => ha (he0.mp h).1
    have hn1 : ((p).ports (a,b)).val≠((p).ports (i,true)).val := fun h => ha (he1.mp h).1
    simp [ha,hn0,hn1]

theorem bit_source (z : Fin (p).count → Bool) (a : Fin (p).count) (b : Bool) :
    bit (m,List.ofFn z) ((p).ports (a,b)).val=(if b then !(z a) else z a) := by
  apply Bool.eq_iff_iff.mpr
  simp only [bit,List.any_eq_true,List.mem_range]
  constructor
  · rintro ⟨i,hi,hc⟩
    have hs := component_source m hg hv z a ⟨i,hi⟩ b
    rw [hs] at hc
    by_cases ha : a=⟨i,hi⟩
    · rw [if_pos ha] at hc
      exact hc
    · rw [if_neg ha] at hc
      exact (Bool.false_ne_true hc).elim
  · intro h
    refine ⟨a.val,a.isLt,?_⟩
    rw [component_source m hg hv z a a b,if_pos rfl]
    exact h

theorem word_source (z : Fin (p).count → Bool) : word (m,List.ofFn z)=List.ofFn ((p).word z) := by
  unfold word
  rw [(RuntimeTensorCatalogue.generated_bounds n m hg).2.2.2.2,
    RuntimeTensorRowsSoundness.map_range_eq_ofFn]
  apply congrArg List.ofFn
  funext j
  obtain ⟨⟨a,b⟩,rfl⟩ := (p).ports.surjective j
  rw [bit_source m hg hv z a b]
  simp only [OrientedPerfectPairing.word,Equiv.symm_apply_apply]

end
end Holant.LocalDrafts.RemoteWork.TractChainV1.RuntimeEOPairWord
