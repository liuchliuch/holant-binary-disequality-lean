import Holant.Proofs.LinearProgramming.Foundation.ExactSolve.DenominatorProgram
import Holant.Proofs.LinearProgramming.Recovery.AllDimensionExactPoint.Source
import Holant.Proofs.LinearProgramming.Support.Average

/-!
One exact maximal-common-support point, constructed from actual LP outputs.
A fixed original call supplies the base. Every coordinate is tested by the
internally emitted denominator threshold; failure reuses that exact base.
Averaging has n+1 terms, including when n=0. This file proves semantics;
CommonSupportProgram supplies the physical compiler and its machine bounds.
-/
open Holant.LocalDrafts.TraversalCompletion.RationalLP
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Support.CommonSupportPoint
open Codec Turing Computability Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines StackProtocol
open Holant.LocalDrafts.RemoteWork.RationalLP.Recovery
open Holant.LocalDrafts.RemoteWork.RationalLP.Foundation
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 32768
set_option Elab.async false
attribute [local irreducible] AllDimensionExactPoint.Source.top

def columnInput (d : Input) (j : Fin d.val.dimension) : Input :=
  ExactSolve.DenominatorProgram.value ⟨d,j⟩
def columnOutput (d : Input) (j : Fin d.val.dimension) : Option (List ℚ) :=
  AllDimensionExactPoint.Source.top (columnInput d j)
def project (d : Input) (j : Fin d.val.dimension) (xs : List ℚ) : Fin d.val.dimension → ℚ :=
  fun k => Codec.point (columnInput d j).val xs k.castSucc

/-- Literal row/RHS equality, projected through nondependent list fields.
The added slack remains the last coordinate; no desired point is input. -/
theorem coefficient_exact (d : Input) (j : Fin d.val.dimension)
    (i : Fin (d.val.rowCount+1)) (k : Fin (d.val.dimension+1)) :
    (columnInput d j).val.coefficient i k=
      Threshold.coefficients d.val j (InputBounds.denominator d.val) i k := by
  have hr := congrArg Raw.rows (ThresholdProgram.raw_exact d j (InputBounds.denominator d.val))
  change ((ThresholdProgram.rawValue (d.val,j.val,InputBounds.denominator d.val)).rows.getD i.val []).getD k.val 0=_
  rw [hr]
  exact Codec.pack_coefficient (d.val.rowCount+1) (d.val.dimension+1)
    (Threshold.coefficients d.val j (InputBounds.denominator d.val)) (Threshold.constants d.val) i k

theorem constant_exact (d : Input) (j : Fin d.val.dimension) (i : Fin (d.val.rowCount+1)) :
    (columnInput d j).val.constant i=Threshold.constants d.val i := by
  have hr := congrArg Raw.rhs (ThresholdProgram.raw_exact d j (InputBounds.denominator d.val))
  change (ThresholdProgram.rawValue (d.val,j.val,InputBounds.denominator d.val)).rhs.getD i.val 0=_
  rw [hr]
  exact Codec.pack_constant (d.val.rowCount+1) (d.val.dimension+1)
    (Threshold.coefficients d.val j (InputBounds.denominator d.val)) (Threshold.constants d.val) i

theorem column_sound (d : Input) (j : Fin d.val.dimension) (xs : List ℚ)
    (he : columnOutput d j=some xs) :
    Codec.Feasible d.val (project d j xs) ∧
      1/(InputBounds.denominator d.val : ℚ)≤project d j xs j := by
  have hs := AllDimensionExactPoint.Source.some_sound (columnInput d j) xs he
  let y := Codec.point (columnInput d j).val xs
  have ht : Codec.Feasible (Threshold.value d.val j (InputBounds.denominator d.val)).val y := by
    apply (Codec.pack_feasible (d.val.rowCount+1) (d.val.dimension+1)
      (Threshold.coefficients d.val j (InputBounds.denominator d.val)) (Threshold.constants d.val) y).mpr
    refine ⟨?_,hs.2.2⟩
    intro i
    rw [← constant_exact d j i]
    calc
      (∑ k, (Threshold.coefficients d.val j (InputBounds.denominator d.val) i k : ℚ) * y k) =
          ∑ k : Fin (d.val.dimension + 1), ((columnInput d j).val.coefficient i k : ℚ) * y k := by
        apply Finset.sum_congr rfl
        intro k _
        rw [coefficient_exact d j i k]
      _ = (columnInput d j).val.constant i := hs.2.1 i
  obtain ⟨hx,h0,h1,hrow⟩ := (Threshold.feasible d.val j _ y).mp ht
  have hD : (0 : ℚ)<InputBounds.denominator d.val := by
    exact_mod_cast InputBounds.denominator_pos d.val
  have hD1 : (1 : ℚ)≤InputBounds.denominator d.val := by
    exact_mod_cast (show 1≤InputBounds.denominator d.val from InputBounds.denominator_pos d.val)
  change (InputBounds.denominator d.val : ℚ)*project d j xs j+
    (1-(InputBounds.denominator d.val : ℚ))*y (Fin.last d.val.dimension)=1 at hrow
  refine ⟨hx,(div_le_iff₀ hD).mpr ?_⟩
  nlinarith

theorem column_complete (d : Input) (j : Fin d.val.dimension) (hp : Codec.Positive d.val j) :
    ∃ xs, columnOutput d j=some xs := by
  obtain ⟨xs,hs,_⟩ := AllDimensionExactPoint.Source.complete (columnInput d j)
    ((ExactSolve.DenominatorProgram.correct ⟨d,j⟩).mp hp)
  exact ⟨xs,hs⟩

/-- Last slot is the actual original point. An unsuccessful column repeats
that SAME original output, so no empty positive-support case is lost. -/
def selected (d : Input) (base : List ℚ) :
    Fin (d.val.dimension+1) → Fin d.val.dimension → ℚ :=
  Fin.lastCases (Codec.point d.val base) (fun j =>
    match columnOutput d j with
    | none => Codec.point d.val base
    | some xs => project d j xs)

def average (d : Input) (base : List ℚ) (j : Fin d.val.dimension) : ℚ :=
  (∑ i, selected d base i j)/(d.val.dimension+1 : ℕ)
def averageList (d : Input) (base : List ℚ) : List ℚ := List.ofFn (average d base)
def value (d : Input) : Option (List ℚ) :=
  (AllDimensionExactPoint.Source.top d).map (averageList d)

theorem selected_feasible (d : Input) (base : List ℚ)
    (hb : AllDimensionExactPoint.Source.top d=some base) (i : Fin (d.val.dimension+1)) :
    Codec.Feasible d.val (selected d base i) := by
  have hbase := (AllDimensionExactPoint.Source.some_sound d base hb).2
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa only [selected,Fin.lastCases_last] using hbase
  · cases he : columnOutput d j with
    | none => simpa only [selected,Fin.lastCases_castSucc,he] using hbase
    | some xs => simpa only [selected,Fin.lastCases_castSucc,he] using (column_sound d j xs he).1

theorem average_feasible (d : Input) (base : List ℚ)
    (hb : AllDimensionExactPoint.Source.top d=some base) :
    Codec.Feasible d.val (average d base) := by
  have hf := selected_feasible d base hb
  have hm : (0 : ℚ)<(d.val.dimension+1 : ℕ) := by positivity
  constructor
  · intro row
    calc
      (∑ j, (d.val.coefficient row j : ℚ)*average d base j)=
          (∑ j, ∑ i, (d.val.coefficient row j : ℚ)*selected d base i j)/(d.val.dimension+1 : ℕ) := by
        simp only [average,mul_div_assoc,Finset.mul_sum,Finset.sum_div]
      _ = (∑ i, ∑ j, (d.val.coefficient row j : ℚ)*selected d base i j)/(d.val.dimension+1 : ℕ) := by
        rw [Finset.sum_comm]
      _ = (∑ _i : Fin (d.val.dimension+1), (d.val.constant row : ℚ))/(d.val.dimension+1 : ℕ) := by
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        exact (hf i).1 row
      _ = d.val.constant row := by
        simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
        field_simp [ne_of_gt hm] <;> ring
  · intro j
    constructor
    · exact div_nonneg (Finset.sum_nonneg (fun i _ => ((hf i).2 j).1)) hm.le
    · apply (div_le_iff₀ hm).mpr
      calc
        (∑ i, selected d base i j)≤∑ _i : Fin (d.val.dimension+1), (1 : ℚ) :=
          Finset.sum_le_sum (fun i _ => ((hf i).2 j).2)
        _ = _ := by simp

theorem average_positive_iff (d : Input) (base : List ℚ)
    (hb : AllDimensionExactPoint.Source.top d=some base) (j : Fin d.val.dimension) :
    0<average d base j ↔ Codec.Positive d.val j := by
  constructor
  · intro hp
    exact ⟨average d base,average_feasible d base hb,hp⟩
  · intro hp
    obtain ⟨xs,hs⟩ := column_complete d j hp
    have hg := (column_sound d j xs hs).2
    have hD : (0 : ℚ)<InputBounds.denominator d.val := by
      exact_mod_cast InputBounds.denominator_pos d.val
    have ht : 0<selected d base j.castSucc j := by
      simpa only [selected,Fin.lastCases_castSucc,hs] using (one_div_pos.mpr hD).trans_le hg
    have hu : selected d base j.castSucc j≤∑ i, selected d base i j :=
      Finset.single_le_sum (fun i _ => ((selected_feasible d base hb i).2 j).1)
        (Finset.mem_univ j.castSucc)
    exact div_pos (ht.trans_le hu) (by positivity)

theorem average_zero_iff (d : Input) (base : List ℚ)
    (hb : AllDimensionExactPoint.Source.top d=some base) (j : Fin d.val.dimension) :
    average d base j=0 ↔ ¬Codec.Positive d.val j := by
  constructor
  · intro hz hp
    have h := (average_positive_iff d base hb j).mpr hp
    simpa only [hz,lt_self_iff_false] using h
  · intro hn
    have h0 := ((average_feasible d base hb).2 j).1
    have h1 : ¬0<average d base j := fun h => hn ((average_positive_iff d base hb j).mp h)
    exact le_antisymm (le_of_not_gt h1) h0

@[simp] theorem point_average (d : Input) (base : List ℚ) :
    Codec.point d.val (averageList d base)=average d base := by
  funext j
  simp [averageList,Codec.point,List.getD_eq_getElem]

theorem none_iff (d : Input) : value d=none ↔ ¬∃ x, Codec.Feasible d.val x := by
  rw [value,Option.map_eq_none_iff,AllDimensionExactPoint.Source.none_iff]

theorem some_properties (d : Input) (xs : List ℚ) (he : value d=some xs) :
    Codec.Solution d.val xs ∧
      (∀ j, 0<Codec.point d.val xs j ↔ Codec.Positive d.val j) ∧
      (∀ j, Codec.point d.val xs j=0 ↔ ¬Codec.Positive d.val j) := by
  obtain ⟨base,hb,rfl⟩ := Option.map_eq_some_iff.mp he
  refine ⟨⟨by simp [averageList],?_⟩,?_,?_⟩
  · simpa only [point_average] using average_feasible d base hb
  · intro j
    simpa only [point_average] using average_positive_iff d base hb j
  · intro j
    simpa only [point_average] using average_zero_iff d base hb j

theorem complete (d : Input) (hf : ∃ x, Codec.Feasible d.val x) :
    ∃ xs, value d=some xs ∧ Codec.Solution d.val xs := by
  obtain ⟨base,hb,_⟩ := AllDimensionExactPoint.Source.complete d hf
  have hv : value d=some (averageList d base) := by rw [value,hb]; rfl
  exact ⟨averageList d base,hv,(some_properties d _ hv).1⟩


end
end Holant.LocalDrafts.RemoteWork.RationalLP.Support.CommonSupportPoint
