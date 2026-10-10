import Holant.Proofs.Tractability.AffineMachine.DensePrograms


namespace Holant.LocalDrafts.Tractability.AffineMachine.PivotPrograms

open Computability Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open FixedGadgetSubstitution.Compiler UniversalPairReduction.SmoothingCompiler
open EncodedTable

abbrev Pivot := Bool × (ℕ × ℕ)
def pivotEncoding := pairEncoding encodingBoolBool
  (pairEncoding UnaryBinary.unaryEncoding UnaryBinary.unaryEncoding)
def bad (r : Row) : Bool := r.1 && r.2.all Bool.not
def badRows (d : Data) : Bool := d.2.1.any bad
def coefficient (d : Data) (r j : ℕ) : Bool := ((d.2.1.getD r (false, [])).2).getD j false
def candidates (d : Data) : List Pivot := (List.range d.2.1.length).flatMap
  (fun r => (List.range d.1).flatMap (fun j => if coefficient d r j then [(true, r, j)] else []))
def selected (d : Data) : Pivot := (candidates d).getD 0 (false, 0, 0)

noncomputable def badComputes : Computes rowEncoding encodingBoolBool bad := by
  let rhs := Wiring.firstComputes encodingBoolBool bitsEncoding
  let coeffs := Wiring.secondComputes encodingBoolBool bitsEncoding
  let neg := ProductMachine.Rewrite.negComputes
  let allZero := ((coeffs.andThen (WireLists.mapComputes encodingBoolBool encodingBoolBool Bool.not neg)).andThen ResidueCells.all)
  exact congrComputes (AccessPrograms.bool Bool.and rhs allZero)
    (fun r => by simp [bad, List.all_map, Function.comp_def])

noncomputable def badRowsComputes : Computes encoding encodingBoolBool badRows :=
  congrComputes ((rows.andThen (WireLists.mapComputes rowEncoding encodingBoolBool bad badComputes)).andThen ResidueCells.any)
    (fun d => by simp [badRows])

noncomputable def coefficientComputes :
    Computes (pairEncoding (pairEncoding encoding UnaryBinary.unaryEncoding) UnaryBinary.unaryEncoding)
      encodingBoolBool (fun x => coefficient x.1.1 x.1.2 x.2) := by
  let pre := Wiring.firstComputes (pairEncoding encoding UnaryBinary.unaryEncoding) UnaryBinary.unaryEncoding
  let d := pre.andThen (Wiring.firstComputes encoding UnaryBinary.unaryEncoding)
  let r := pre.andThen (Wiring.secondComputes encoding UnaryBinary.unaryEncoding)
  let j := Wiring.secondComputes (pairEncoding encoding UnaryBinary.unaryEncoding) UnaryBinary.unaryEncoding
  let row := AccessPrograms.get rowEncoding (false, []) (d.andThen rows) r
  exact AccessPrograms.get encodingBoolBool false
    (row.andThen (Wiring.secondComputes encodingBoolBool bitsEncoding)) j

noncomputable def cell :
    Computes (pairEncoding (pairEncoding encoding UnaryBinary.unaryEncoding) UnaryBinary.unaryEncoding)
      (framedListEncoding pivotEncoding)
      (fun x => if coefficient x.1.1 x.1.2 x.2 then [(true, x.1.2, x.2)] else []) := by
  let ea := pairEncoding (pairEncoding encoding UnaryBinary.unaryEncoding) UnaryBinary.unaryEncoding
  let pre := Wiring.firstComputes (pairEncoding encoding UnaryBinary.unaryEncoding) UnaryBinary.unaryEncoding
  let r := pre.andThen (Wiring.secondComputes encoding UnaryBinary.unaryEncoding)
  let j := Wiring.secondComputes (pairEncoding encoding UnaryBinary.unaryEncoding) UnaryBinary.unaryEncoding
  let pair := pairComputes (constantComputes ea encodingBoolBool true) (pairComputes r j)
  let singleton := fixedListComputes ea pivotEncoding (fun x (_ : Unit) => (true, x.1.2, x.2)) (fun _ => pair) [()]
  exact ifComputes coefficientComputes (congrComputes singleton (fun _ => rfl)) (constantComputes ea _ [])

noncomputable def candidatesComputes : Computes encoding (framedListEncoding pivotEncoding) candidates := by
  let rowLists := (WireLists.tabulate (pairEncoding encoding UnaryBinary.unaryEncoding)
    (framedListEncoding pivotEncoding) (fun x => x.1.1)
    ((Wiring.firstComputes encoding UnaryBinary.unaryEncoding).andThen count) (fun x j => if coefficient x.1 x.2 j then [(true, x.2, j)] else []) cell).andThen
      (WireLists.flatten pivotEncoding)
  let allRows := (WireLists.tabulate encoding (framedListEncoding pivotEncoding)
    (fun d => d.2.1.length) (rows.andThen (WireLists.lengthComputes rowEncoding))
    (fun d r => ((List.range d.1).map (fun j => if coefficient d r j then [(true, r, j)] else [])).flatten) rowLists).andThen
      (WireLists.flatten pivotEncoding)
  exact congrComputes allRows (fun d => by simp [candidates, List.flatMap_def])

noncomputable def computes : Computes encoding pivotEncoding selected :=
  candidatesComputes.andThen (getDComputes pivotEncoding 0 (false, 0, 0))

theorem candidate_spec (d : Data) (p : Pivot) : p ∈ candidates d ↔
    p.1 = true ∧ p.2.1 < d.2.1.length ∧ p.2.2 < d.1 ∧ coefficient d p.2.1 p.2.2 = true := by
  simp [candidates, List.mem_flatMap]
  constructor
  · rintro ⟨r, hr, j, hj, h⟩
    rcases h with ⟨hv, rfl⟩
    exact ⟨rfl, hr, hj, hv⟩
  · rintro ⟨ht, hr, hj, hv⟩
    exact ⟨p.2.1, hr, p.2.2, hj, by simp [hv, ← ht]⟩

theorem selected_valid (d : Data) (h : (selected d).1 = true) :
    (selected d).2.1 < d.2.1.length ∧ (selected d).2.2 < d.1 ∧
      coefficient d (selected d).2.1 (selected d).2.2 = true := by
  cases hs : candidates d with
  | nil => simp [selected, hs] at h
  | cons p ps =>
    have hp := (candidate_spec d p).mp (by simp [hs])
    simpa [selected, hs] using hp.2

theorem selected_none (d : Data) (h : (selected d).1 = false) :
    ∀ r < d.2.1.length, ∀ j < d.1, coefficient d r j = false := by
  intro r hr j hj
  cases hv : coefficient d r j with
  | false => rfl
  | true =>
    have hm := (candidate_spec d (true, r, j)).mpr ⟨rfl, hr, hj, hv⟩
    cases hs : candidates d with
    | nil => simp [hs] at hm
    | cons p ps =>
      have hp := (candidate_spec d p).mp (by simp [hs])
      simp [selected, hs, hp.1] at h

end Holant.LocalDrafts.Tractability.AffineMachine.PivotPrograms
