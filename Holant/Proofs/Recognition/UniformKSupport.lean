import Holant.Proofs.Recognition.UniformKPolynomial
import Holant.Proofs.Recognition.PhysicalFolds

/-!
# Uniform original-descriptor support and layer decisions after K inverse

The single physical input is the old original-family RootCode word. Every
K-entry zero test is a two-sided polynomial-system search in the ORIGINAL
bindings. Finite folds produce both weak support signs and the full per-label
single-layer decision. No coefficient field, transformed descriptor, desired
answer, matrix witness or caller-supplied evaluator occurs in the programme.

This is the complete support/layer part of source clauses (1)/(2). Their EO
class constraints and all seven/four alternatives are separate obligations.
-/
namespace Holant.LocalDrafts.RemoteWork.TractChainV1.UniformKSupport
open Turing Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.MainChain.TransformRecognition
open Holant.LocalDrafts.RemoteWork.TractChainV1.PhysicalFolds
noncomputable section

structure Data (s : ℕ) (arity : Fin s → ℕ) where
  input : OriginalFamilyInput.Input arity
  G : (i : Fin s) → Signature AlgebraicComplex (arity i)
  represented : ∀ i x, (input i x).Represents (G i x : ℂ)

variable {s : ℕ} (arity : Fin s → ℕ)
def original (d : Data s arity) : OriginalFamilyPackingMachine.Input :=
  OriginalFamilyPackingSource.fromSource arity d.input false

def zero (d : Data s arity) (i : Fin s) (x : Fin (arity i) → Bool) : Bool :=
  UniformKPolynomial.answer arity d.G d.input d.represented i x

def zeroRuns (i : Fin s) (x : Fin (arity i) → Bool) :
    Runs OriginalFamilyPackingMachine.encoding encodingBoolBool
      (original arity) (fun d => zero arity d i x) where
  machine := UniformKPolynomial.machine arity i x
  cost d := Classical.choose (UniformKPolynomial.source_outputs arity d.G d.input d.represented i x)
  outputs d := Classical.choice (Classical.choose_spec
    (UniformKPolynomial.source_outputs arity d.G d.input d.represented i x))

theorem zero_correct (d : Data s arity) (i : Fin s) (x : Fin (arity i) → Bool) :
    zero arity d i x=true ↔ sourceKBasis.symm.action (d.G i) x=0 :=
  UniformKPolynomial.answer_correct arity d.G d.input d.represented i x

def signHolds (negative : Bool) {n : ℕ} (x : Fin n → Bool) : Prop :=
  if negative then Holant.charge x≤0 else 0≤Holant.charge x
instance (negative : Bool) {n : ℕ} (x : Fin n → Bool) : Decidable (signHolds negative x) := by
  unfold signHolds
  infer_instance

def sideCell (negative : Bool) (i : Fin s) (x : Fin (arity i) → Bool) (d : Data s arity) : Bool :=
  if signHolds negative x then true else zero arity d i x

def sideCellRuns (negative : Bool) (i : Fin s) (x : Fin (arity i) → Bool) :
    Runs OriginalFamilyPackingMachine.encoding encodingBoolBool (original arity)
      (sideCell arity negative i x) := by
  by_cases h : signHolds negative x
  · exact (Runs.constant _ _ (original arity) true).congr (fun _ => by simp [sideCell,h])
  · exact (zeroRuns arity i x).congr (fun _ => by simp [sideCell,h])

def side (negative : Bool) (d : Data s arity) : Bool :=
  (List.finRange s).all (fun i => (SparseTransform.allWords (arity i)).all
    (fun x => sideCell arity negative i x d))

def sideRuns (negative : Bool) : Runs OriginalFamilyPackingMachine.encoding encodingBoolBool
    (original arity) (side arity negative) :=
  Runs.all (fun d i => (SparseTransform.allWords (arity i)).all
      (fun x => sideCell arity negative i x d))
    (fun i => Runs.all (fun d x => sideCell arity negative i x d)
      (fun x => sideCellRuns arity negative i x) (SparseTransform.allWords (arity i))) (List.finRange s)

theorem side_correct (negative : Bool) (d : Data s arity) :
    side arity negative d=true ↔
      ∀ i x, sourceKBasis.symm.action (d.G i) x≠0 → signHolds negative x := by
  have hcell (i : Fin s) (x : Fin (arity i) → Bool) :
      sideCell arity negative i x d=true ↔
        sourceKBasis.symm.action (d.G i) x≠0 → signHolds negative x := by
    by_cases h : signHolds negative x
    · simp [sideCell,h]
    · simp [sideCell,h,zero_correct]
  simp only [side,List.all_eq_true,List.mem_finRange,forall_true_left,
    SparseTransform.mem_allWords,hcell]

def layerCell (layer : ℕ) (i : Fin s) (x : Fin (arity i) → Bool) (d : Data s arity) : Bool :=
  if Holant.weight x=layer then true else zero arity d i x

def layerCellRuns (layer : ℕ) (i : Fin s) (x : Fin (arity i) → Bool) :
    Runs OriginalFamilyPackingMachine.encoding encodingBoolBool (original arity)
      (layerCell arity layer i x) := by
  by_cases h : Holant.weight x=layer
  · exact (Runs.constant _ _ (original arity) true).congr (fun _ => by simp [layerCell,h])
  · exact (zeroRuns arity i x).congr (fun _ => by simp [layerCell,h])

def layer (k : ℕ) (i : Fin s) (d : Data s arity) : Bool :=
  (SparseTransform.allWords (arity i)).all (fun x => layerCell arity k i x d)

def layerRuns (k : ℕ) (i : Fin s) : Runs OriginalFamilyPackingMachine.encoding encodingBoolBool
    (original arity) (layer arity k i) :=
  Runs.all (fun d x => layerCell arity k i x d) (fun x => layerCellRuns arity k i x)
    (SparseTransform.allWords (arity i))

theorem layer_correct (k : ℕ) (i : Fin s) (d : Data s arity) :
    layer arity k i d=true ↔ Signature.SingleLayer (sourceKBasis.symm.action (d.G i)) k := by
  simp only [layer,List.all_eq_true,SparseTransform.mem_allWords,forall_true_left,
    layerCell,Signature.SingleLayer]
  constructor
  · intro h x hx
    apply (zero_correct arity d i x).mp
    simpa only [if_neg hx] using h x
  · intro h x
    by_cases hx : Holant.weight x=k
    · simp [hx]
    · simp only [if_neg hx]
      exact (zero_correct arity d i x).mpr (h x hx)

def someLayer (i : Fin s) (d : Data s arity) : Bool :=
  (List.range (arity i+1)).any (fun k => layer arity k i d)

def someLayerRuns (i : Fin s) : Runs OriginalFamilyPackingMachine.encoding encodingBoolBool
    (original arity) (someLayer arity i) :=
  Runs.any (fun d k => layer arity k i d) (fun k => layerRuns arity k i) (List.range (arity i+1))

private theorem layer_bounded {n : ℕ} (f : Signature AlgebraicComplex n) :
    (∃ k, Signature.SingleLayer f k) ↔ ∃ k≤n, Signature.SingleLayer f k := by
  classical
  constructor
  · rintro ⟨k,hk⟩
    by_cases hf : f=0
    · exact ⟨0,Nat.zero_le _,by simp [hf,Signature.SingleLayer]⟩
    · have hx : ∃ x, f x≠0 := by
        by_contra h
        push_neg at h
        exact hf (funext h)
      obtain ⟨x,hx⟩ := hx
      have hw : weight x=k := by
        by_contra hn
        exact hx (hk x hn)
      exact ⟨k,hw ▸ Holant.weight_le x,hk⟩
  · rintro ⟨k,_,hk⟩; exact ⟨k,hk⟩

theorem someLayer_correct (i : Fin s) (d : Data s arity) :
    someLayer arity i d=true ↔ ∃ k, Signature.SingleLayer (sourceKBasis.symm.action (d.G i)) k := by
  rw [layer_bounded]
  simp only [someLayer,List.any_eq_true,List.mem_range,layer_correct,Nat.lt_succ_iff]

def allLayers (d : Data s arity) : Bool := (List.finRange s).all (fun i => someLayer arity i d)
def allLayersRuns : Runs OriginalFamilyPackingMachine.encoding encodingBoolBool
    (original arity) (allLayers arity) :=
  Runs.all (fun d i => someLayer arity i d) (fun i => someLayerRuns arity i) (List.finRange s)

theorem allLayers_correct (d : Data s arity) :
    allLayers arity d=true ↔ ∀ i, ∃ k, Signature.SingleLayer (sourceKBasis.symm.action (d.G i)) k := by
  simp only [allLayers,List.all_eq_true,List.mem_finRange,forall_true_left,someLayer_correct]

abbrev outputEncoding := pairEncoding encodingBoolBool (pairEncoding encodingBoolBool encodingBoolBool)
def output (d : Data s arity) : Bool × (Bool × Bool) :=
  (side arity false d,side arity true d,allLayers arity d)
def executes : Runs OriginalFamilyPackingMachine.encoding outputEncoding (original arity) (output arity) :=
  (sideRuns arity false).pair ((sideRuns arity true).pair (allLayersRuns arity))

/-- Exactly one programme emits all three answers on the same original word.
The two weak signs also decide both-strict-sign support by finite negation. -/
theorem source (d : Data s arity) :
    Nonempty (TM2OutputsInTime (executes arity).machine.computer
      (OriginalFamilyPackingMachine.encoding.encode (original arity d))
      (some (outputEncoding.encode (output arity d))) ((executes arity).cost d)) ∧
    ((output arity d).1=true ↔ ∀ i x, sourceKBasis.symm.action (d.G i) x≠0 → 0≤Holant.charge x) ∧
    ((output arity d).2.1=true ↔ ∀ i x, sourceKBasis.symm.action (d.G i) x≠0 → Holant.charge x≤0) ∧
    ((output arity d).2.2=true ↔ ∀ i, ∃ k, Signature.SingleLayer (sourceKBasis.symm.action (d.G i)) k) := by
  exact ⟨⟨(executes arity).outputs d⟩,side_correct arity false d,side_correct arity true d,
    allLayers_correct arity d⟩

end
end Holant.LocalDrafts.RemoteWork.TractChainV1.UniformKSupport
