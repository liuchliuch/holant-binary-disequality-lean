import Holant.Proofs.Recognition.UniformTensorWitnessBranch

/-!
# Physical first-success tensor-witness emission

Each successful nonzero label receives the first accepted ordered shape/pivot
and the actual algebraic polynomial witness. Zero signatures receive an explicit
zero flag. The finite selectors preserve the returned packet without selecting
new coefficients. Every candidate machine is the original-root branch machine.
-/

namespace Holant.LocalDrafts.RemoteWork.TractChainV1.UniformTensorWitness

open Turing Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing GraphPreprocessing.OriginalCoefficient
open UniversalPairReduction.SmoothingCompiler
open Holant.LocalDrafts.MainChain.TransformRecognition
open Holant.LocalDrafts.EffectiveAlgebraic
open PhysicalFolds UniformTensorDecisionBranch UniformTensorWitnessBranch
noncomputable section
set_option backward.isDefEq.respectTransparency false

private def presence : Computes resultEncoding encodingBoolBool Option.isSome :=
  congrComputes ((OptionMap.computes (constantComputes packetEncoding encodingBoolBool true)).andThen
    OptionAny.computes) (fun q => by cases q <;> rfl)

/-- Retain the first actual present packet; the two incoming payloads are unchanged. -/
def firstComputes : Computes (pairEncoding resultEncoding resultEncoding) resultEncoding
    (fun p : Option Packet × Option Packet => p.1.or p.2) := by
  let left := Wiring.firstComputes resultEncoding resultEncoding
  let right := Wiring.secondComputes resultEncoding resultEncoding
  apply congrComputes (ifComputes (left.andThen presence) left right)
  rintro ⟨p,q⟩
  cases p <;> rfl

def first {D C : Type} (f : C → D → Option Packet) : List C → D → Option Packet
  | [],_ => none
  | c::cs,d => (f c d).or (first f cs d)

def firstRuns {D A C : Type} {ea : Encoding A Bool} {input : D → A}
    (f : C → D → Option Packet) (w : ∀ c, Runs ea resultEncoding input (f c)) :
    (cs : List C) → Runs ea resultEncoding input (first f cs)
  | [] => Runs.constant ea resultEncoding input none
  | c::cs => (w c |>.pair (firstRuns f w cs)).after firstComputes

theorem first_isSome {D C : Type} (f : C → D → Option Packet) (cs : List C) (d : D) :
    (first f cs d).isSome = true ↔ ∃ c ∈ cs, (f c d).isSome = true := by
  induction cs with
  | nil => simp [first]
  | cons c cs ih =>
    cases h : f c d <;> simp [first,h,ih]

theorem first_origin {D C : Type} (f : C → D → Option Packet) (cs : List C) (d : D) (p : Packet)
    (hp : first f cs d = some p) : ∃ c ∈ cs, f c d = some p := by
  induction cs with
  | nil => simp [first] at hp
  | cons c cs ih =>
    cases h : f c d with
    | none =>
      have ht : first f cs d = some p := by simpa [first,h] using hp
      obtain ⟨c',hc',he⟩ := ih ht
      exact ⟨c',List.mem_cons_of_mem _ hc',he⟩
    | some q =>
      have hq : q = p := by simpa [first,h] using hp
      exact ⟨c,List.mem_cons_self,by simpa [hq] using h⟩

abbrev LabelCertificate := Bool × Option Packet
abbrev labelEncoding := pairEncoding encodingBoolBool resultEncoding

def accepted (c : LabelCertificate) : Bool := c.1 || c.2.isSome

variable {s : ℕ} (arity : Fin s → ℕ)

def arityChoices (n : ℕ) := (UniformTensorDecision.arityShapes n).flatMap
  (fun S => (SparseTransform.allWords n).map (fun p => (S,p)))
def matchingChoices (n : ℕ) := (UniformTensorDecision.matchingShapes n).flatMap
  (fun S => (SparseTransform.allWords n).map (fun p => (S,p)))

def arityCell (i : Fin s) (c : TensorDecision.Shape (arity i) × (Fin (arity i) → Bool)) :
    Data s arity → Option Packet :=
  UniformTensorWitnessBranch.output arity false (table arity none i)
    c.1.count c.1.arity c.1.ports c.2

def arityCellRuns (i : Fin s) (c : TensorDecision.Shape (arity i) × (Fin (arity i) → Bool)) :
    Runs OriginalFamilyPackingMachine.encoding resultEncoding (original arity) (arityCell arity i c) :=
  runs arity false (table arity none i) c.1.count c.1.arity c.1.ports c.2

def arityNonzero (i : Fin s) := first (arityCell arity i) (arityChoices (arity i))
def arityNonzeroRuns (i : Fin s) := firstRuns (arityCell arity i) (arityCellRuns arity i) (arityChoices (arity i))

def arityLabel (i : Fin s) (d : Data s arity) : LabelCertificate :=
  (UniformTensorDecision.allZero arity none i d,arityNonzero arity i d)
def arityLabelRuns (i : Fin s) : Runs OriginalFamilyPackingMachine.encoding labelEncoding
    (original arity) (arityLabel arity i) :=
  (UniformTensorDecision.allZeroRuns arity none i).pair (arityNonzeroRuns arity i)

theorem arityLabel_correct (i : Fin s) (d : Data s arity) :
    accepted (arityLabel arity i d) = true ↔ SourceTensorClosure (fun n _ => n = 1 ∨ n = 2) (d.G i) := by
  rw [TensorDecisionCleared.arityTwo_source_iff]
  simp only [accepted,arityLabel,Bool.or_eq_true,UniformTensorDecision.allZero_correct,
    arityNonzero,first_isSome,arityChoices,List.mem_flatMap,List.mem_map,
    UniformTensorDecision.mem_arityShapes,SparseTransform.mem_allWords,true_and,
    arityCell,UniformTensorWitnessBranch.output_isSome_iff]
  constructor
  · rintro (hz | ⟨c,⟨S,p,hc⟩,h⟩)
    · exact Or.inl hz
    · subst c
      exact Or.inr ⟨S,p,(UniformTensorDecision.arityBranch_correct arity i S p d).mp h⟩
  · rintro (hz | ⟨S,p,h⟩)
    · exact Or.inl hz
    · exact Or.inr ⟨(S,p),⟨S,p,rfl⟩,(UniformTensorDecision.arityBranch_correct arity i S p d).mpr h⟩

theorem arity_origin (i : Fin s) (d : Data s arity) (p : Packet)
    (hp : arityNonzero arity i d = some p) :
    ∃ S : TensorDecision.Shape (arity i), ∃ pivot : Fin (arity i) → Bool,
      p.1 = metadata S.count S.arity S.ports pivot ∧
      raw arity false (table arity none i) S.count S.arity S.ports pivot d = some p.2 := by
  obtain ⟨c,_,hc⟩ := first_origin (arityCell arity i) (arityChoices (arity i)) d p hp
  exact ⟨c.1,c.2,output_metadata arity false _ _ _ _ _ d p hc⟩

def matchingCell (opposite : Bool) (i : Fin s)
    (c : TensorDecisionStable.Shape (arity i) × (Fin (arity i) → Bool)) : Data s arity → Option Packet :=
  UniformTensorWitnessBranch.output arity true (table arity (some opposite) i)
    c.1.count c.1.arity c.1.ports c.2

def matchingCellRuns (opposite : Bool) (i : Fin s)
    (c : TensorDecisionStable.Shape (arity i) × (Fin (arity i) → Bool)) :
    Runs OriginalFamilyPackingMachine.encoding resultEncoding (original arity) (matchingCell arity opposite i c) :=
  runs arity true (table arity (some opposite) i) c.1.count c.1.arity c.1.ports c.2

def matchingNonzero (opposite : Bool) (i : Fin s) :=
  first (matchingCell arity opposite i) (matchingChoices (arity i))
def matchingNonzeroRuns (opposite : Bool) (i : Fin s) :=
  firstRuns (matchingCell arity opposite i) (matchingCellRuns arity opposite i) (matchingChoices (arity i))

def matchingLabel (opposite : Bool) (i : Fin s) (d : Data s arity) : LabelCertificate :=
  (UniformTensorDecision.allZero arity (some opposite) i d,matchingNonzero arity opposite i d)
def matchingLabelRuns (opposite : Bool) (i : Fin s) : Runs OriginalFamilyPackingMachine.encoding labelEncoding
    (original arity) (matchingLabel arity opposite i) :=
  (UniformTensorDecision.allZeroRuns arity (some opposite) i).pair (matchingNonzeroRuns arity opposite i)

theorem matchingLabel_correct (opposite : Bool) (i : Fin s) (d : Data s arity) :
    accepted (matchingLabel arity opposite i d) = true ↔ SourceTensorClosure (matchingImage opposite) (d.G i) := by
  rw [TensorDecisionCleared.matching_source_iff]
  simp only [accepted,matchingLabel,Bool.or_eq_true,UniformTensorDecision.allZero_correct,
    matchingNonzero,first_isSome,matchingChoices,List.mem_flatMap,List.mem_map,
    UniformTensorDecision.mem_matchingShapes,SparseTransform.mem_allWords,true_and,
    matchingCell,UniformTensorWitnessBranch.output_isSome_iff]
  constructor
  · rintro (hz | ⟨c,⟨S,p,hc⟩,h⟩)
    · exact Or.inl hz
    · subst c
      exact Or.inr ⟨S,p,(UniformTensorDecision.matchingBranch_correct arity opposite i S p d).mp h⟩
  · rintro (hz | ⟨S,p,h⟩)
    · exact Or.inl hz
    · exact Or.inr ⟨(S,p),⟨S,p,rfl⟩,(UniformTensorDecision.matchingBranch_correct arity opposite i S p d).mpr h⟩

theorem matching_origin (opposite : Bool) (i : Fin s) (d : Data s arity) (p : Packet)
    (hp : matchingNonzero arity opposite i d = some p) :
    ∃ S : TensorDecisionStable.Shape (arity i), ∃ pivot : Fin (arity i) → Bool,
      p.1 = metadata S.count S.arity S.ports pivot ∧
      raw arity true (table arity (some opposite) i) S.count S.arity S.ports pivot d = some p.2 := by
  obtain ⟨c,_,hc⟩ := first_origin (matchingCell arity opposite i) (matchingChoices (arity i)) d p hp
  exact ⟨c.1,c.2,output_metadata arity true _ _ _ _ _ d p hc⟩

/-- The zero flag certifies the literal original table, including nullary zero. -/
theorem arity_zero_iff (i : Fin s) (d : Data s arity) :
    (arityLabel arity i d).1 = true ↔ d.G i = 0 := by
  rw [arityLabel,UniformTensorDecision.allZero_correct]
  exact ⟨fun h => funext h,fun h x => congrFun h x⟩

/-- A present packet identifies a genuine accepted input-slice factorization. -/
theorem arity_packet_correct (i : Fin s) (d : Data s arity) (p : Packet)
    (hp : arityNonzero arity i d = some p) :
    ∃ S : TensorDecision.Shape (arity i), ∃ pivot : Fin (arity i) → Bool,
      p.1 = metadata S.count S.arity S.ports pivot ∧
      TensorDecisionCleared.ArityTwoAccepts (d.G i) S pivot ∧
      raw arity false (table arity none i) S.count S.arity S.ports pivot d = some p.2 := by
  obtain ⟨S,pivot,hm,hr⟩ := arity_origin arity i d p hp
  have ha := (raw_isSome_iff arity false (table arity none i) S.count S.arity S.ports pivot d).mp
    (by rw [hr]; rfl)
  exact ⟨S,pivot,hm,(UniformTensorDecision.arityBranch_correct arity i S pivot d).mp ha,hr⟩

/-- Matching packets use the specified common orientation and literal transformed table. -/
theorem matching_packet_correct (opposite : Bool) (i : Fin s) (d : Data s arity) (p : Packet)
    (hp : matchingNonzero arity opposite i d = some p) :
    ∃ S : TensorDecisionStable.Shape (arity i), ∃ pivot : Fin (arity i) → Bool,
      p.1 = metadata S.count S.arity S.ports pivot ∧
      TensorDecisionCleared.OneHotAccepts ((TensorDecisionMatching.basis opposite).symm.action (d.G i)) S pivot ∧
      raw arity true (table arity (some opposite) i) S.count S.arity S.ports pivot d = some p.2 := by
  obtain ⟨S,pivot,hm,hr⟩ := matching_origin arity opposite i d p hp
  have ha := (raw_isSome_iff arity true (table arity (some opposite) i) S.count S.arity S.ports pivot d).mp
    (by rw [hr]; rfl)
  exact ⟨S,pivot,hm,(UniformTensorDecision.matchingBranch_correct arity opposite i S pivot d).mp ha,hr⟩

end
end Holant.LocalDrafts.RemoteWork.TractChainV1.UniformTensorWitness
