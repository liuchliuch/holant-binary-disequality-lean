import Holant.Proofs.Tractability.AffineMachine.AccessPrograms


namespace Holant.LocalDrafts.Tractability.LocalAffineMachine.Relabel.WordLookup

open Computability Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open FixedGadgetSubstitution.Compiler AffineMachine

def wordEncoding := framedListEncoding encodingBoolBool
def inputEncoding := pairEncoding wordEncoding encodingNatBool

def scanned (x : List Bool × ℕ) : Bool :=
  ((List.range x.1.length).map (fun j => decide (j = x.2) && x.1.getD j false)).any id

theorem scanned_eq (x : List Bool × ℕ) : scanned x = x.1.getD x.2 false := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    obtain ⟨a, ha, hb⟩ := List.any_eq_true.mp h
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ha
    obtain ⟨he, hv⟩ := Bool.and_eq_true_iff.mp hb
    have he' : j = x.2 := of_decide_eq_true he
    simpa [he'] using hv
  · intro h
    have hi : x.2 < x.1.length := by
      by_contra hn
      have hd := List.getD_eq_default x.1 false (Nat.le_of_not_gt hn)
      rw [hd] at h
      contradiction
    apply List.any_eq_true.mpr
    refine ⟨true, ?_, rfl⟩
    exact List.mem_map.mpr ⟨x.2, List.mem_range.mpr hi, by simpa only [decide_true, Bool.true_and] using h⟩

noncomputable def computes : Computes inputEncoding encodingBoolBool (fun x => x.1.getD x.2 false) := by
  let word := Wiring.firstComputes wordEncoding encodingNatBool
  let address := Wiring.secondComputes wordEncoding encodingNatBool
  let context := Wiring.firstComputes inputEncoding UnaryBinary.unaryEncoding
  let j := Wiring.secondComputes inputEncoding UnaryBinary.unaryEncoding
  let eq := AccessPrograms.eqNat (j.andThen UnaryBinary.computes) (context.andThen address)
  let bit := AccessPrograms.get encodingBoolBool false (context.andThen word) j
  let cells := WireLists.tabulate inputEncoding encodingBoolBool (fun x => x.1.length)
    (word.andThen (WireLists.lengthComputes encodingBoolBool)) (fun x j => decide (j = x.2) && x.1.getD j false) (AccessPrograms.bool Bool.and eq bit)
  exact congrComputes (cells.andThen ResidueCells.any) scanned_eq

theorem word_length (w : List Bool) : (wordEncoding.encode w).length = 4 * w.length + 1 := by
  induction w with
  | nil => rfl
  | cons bit w ih =>
    cases bit <;> simp_all [wordEncoding, framedListEncoding, framedListEncode, Holant.Algebraic.frame, encodingBoolBool, encodeBool] <;> omega

theorem input_length (x : List Bool × ℕ) :
    (inputEncoding.encode x).length = 8 * x.1.length + x.2.size + 3 := by
  simp [inputEncoding, pairEncoding_length, word_length, encodingNatBool, Holant.Algebraic.encodeNat_length]
  omega

theorem primitive_bound (x : List Bool × ℕ) :
    primitiveCost computes.machine (computes.outputs x).steps
      (some (Turing.initList computes.machine.computer (inputEncoding.encode x))) ≤
        (primitivePolynomial computes).eval (inputEncoding.encode x).length := computes_primitive_cost computes x

end Holant.LocalDrafts.Tractability.LocalAffineMachine.Relabel.WordLookup
