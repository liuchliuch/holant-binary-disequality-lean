import Holant.Proofs.Hardness.PairedPinsSemantics
import Holant.Complexity.FixedGadgetSubstitution.Compiler.Compile

/-! Exact balance transport through the literal fixed-template compiler.
This lemma is about graph records and actual local occurrence counts. The
unit-macro producer must establish those counts internally; no hardness,
value, unary-access or target compiler theorem is an input. -/
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.PairedPinsExpansionBalance
open Holant Holant.Complexity FixedGadgetSubstitution
open PairedPinsRaw

private theorem place_count (t : Template) (off : ℕ) (ports : List RawEndpoint) (label : ℕ) :
    ((t.placeVertices off ports).filter (fun row => row.1=label)).length=
      (t.vertices.filter (fun row => row.1=label)).length := by
  unfold Template.placeVertices
  generalize t.vertices=xs
  induction xs with
  | nil => rfl
  | cons row xs ih => by_cases h : row.1=label <;> simp [h,ih]

private theorem expand_count (ts : ℕ → Template) (off : ℕ) (xs : List RawVertex) (label : ℕ) :
    ((expandRows ts off xs).vertices.filter (fun row => row.1=label)).length=
      (xs.map (fun row => ((ts row.1).vertices.filter (fun q => q.1=label)).length)).sum := by
  induction xs generalizing off with
  | nil => rfl
  | cons row xs ih => simp [expandRows,List.filter_append,place_count,ih]

private theorem two_label_sum (xs : List RawVertex) (u v : ℕ)
    (h : ∀row∈xs,row.1<2) :
    (xs.map (fun row => if row.1=0 then u else v)).sum=
      u*(xs.filter (fun row => row.1=0)).length+
      v*(xs.filter (fun row => row.1=1)).length := by
  induction xs with
  | nil => simp
  | cons row xs ih =>
      have hr := h row (by simp)
      have ht := ih (fun x hx => h x (by simp [hx]))
      have cases : row.1=0 ∨ row.1=1 := by omega
      rcases cases with hz|ho
      · simp [hz,ht,Nat.mul_add,Nat.mul_succ]
        omega
      · simp [ho,ht,Nat.mul_add,Nat.mul_succ]
        omega

variable {s b : ℕ} {a sourceA : ℕ → ℕ}
variable (ts : ℕ → Template)
variable (hts : ∀i<2,(ts i).WellFormed (s+2) b (sourceArity s a) ∧ (ts i).boundary=sourceA i)
variable (hprofile : ∀i<2,∀bit : Bool,
  ((ts i).vertices.filter (fun row => row.1=s+bit.toNat)).length=
    if i=0 then (if bit then 2 else 3) else (if bit then 3 else 2))

/-- This is the output of the already proved actual fixed-template compiler. -/
def expanded (r : ExactSignatureTables.Input 2 b sourceA) :
    ExactSignatureTables.Input (s+2) b (sourceArity s a) :=
  Compiler.value 2 b sourceA ts (s+2) (sourceArity s a) hts r

include hprofile in
theorem pins_length (r : ExactSignatureTables.Input 2 b sourceA) (bit : Bool) :
    (pins s bit (expanded ts hts r).val).length=
      (if bit then 2 else 3)*(r.val.vertices.filter (fun row => row.1=0)).length+
      (if bit then 3 else 2)*(r.val.vertices.filter (fun row => row.1=1)).length := by
  rw [PairedPinsSemantics.pins_length_eq_count (expanded ts hts r).property bit]
  change ((expandRows ts r.val.edges.length r.val.vertices).vertices.filter
    (fun row => row.1=s+bit.toNat)).length=_
  rw [expand_count]
  have hrange : ∀row∈r.val.vertices,row.1<2 := by
    intro row hr
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hr
    exact (r.property.1 i).1
  have he : r.val.vertices.map (fun row =>
      ((ts row.1).vertices.filter (fun q => q.1=s+bit.toNat)).length)=
    r.val.vertices.map (fun row => if row.1=0 then (if bit then 2 else 3) else (if bit then 3 else 2)) := by
    apply List.map_congr_left
    intro row hr
    exact hprofile row.1 (hrange row hr) bit
  rw [he]
  exact two_label_sum _ _ _ hrange

include hprofile in
/-- Actual source label balance, including zero-value and empty inputs,
forces balance of the compiler's concrete emitted pin endpoint lists. -/
theorem balanced (r : ExactSignatureTables.Input 2 b sourceA)
    (hb : (r.val.vertices.filter (fun row => row.1=0)).length=
      (r.val.vertices.filter (fun row => row.1=1)).length) :
    Balanced s (expanded ts hts r).val := by
  unfold Balanced
  rw [pins_length ts hts hprofile r false,pins_length ts hts hprofile r true,hb]
  simp only [Bool.false_eq_true,ite_false,ite_true]
  omega

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.PairedPinsExpansionBalance
