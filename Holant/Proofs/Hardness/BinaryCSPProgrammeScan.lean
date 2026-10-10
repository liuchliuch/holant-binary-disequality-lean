import Holant.Proofs.Hardness.BinaryCSPProgrammeStars
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.FirstTrue

/-! Finite tape scans for occurrence-cycle successors. All list positions are
physical unary words. Binary variable names are only compared or copied, never
used as unbounded iteration counts. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryCSPProgrammeScan
open Turing Computability Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open BinaryCSPProgrammeCore
open FixedGadgetSubstitution.Compiler UniversalPairReduction.SmoothingCompiler
namespace W
export Holant.LocalDrafts.Tractability.AffineMachine.WireLists (tabulate flatten lengthComputes succComputes getD)
end W
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false

abbrev positionsEncoding := framedListEncoding unary
abbrev addressesEncoding := framedListEncoding encodingNatBool
abbrev occurrenceEncoding := pairEncoding addressesEncoding encodingNatBool

def occurrences (addresses : List ℕ) (address : ℕ) : List ℕ :=
  (List.range addresses.length).filter (fun i => addresses.getD i 0=address)

def occurrencesComputes : Computes occurrenceEncoding positionsEncoding
    (fun x => occurrences x.1 x.2) := by
  let context := Wiring.firstComputes occurrenceEncoding unary
  let addresses := context.andThen (Wiring.firstComputes addressesEncoding encodingNatBool)
  let target := context.andThen (Wiring.secondComputes addressesEncoding encodingNatBool)
  let i := Wiring.secondComputes occurrenceEncoding unary
  let entry := (pairComputes addresses i).andThen (W.getD encodingNatBool 0)
  let test := (pairComputes entry target).andThen Endpoints.equalComputes
  let cell : Computes (pairEncoding occurrenceEncoding unary) positionsEncoding
      (fun x => if x.1.1.getD x.2 0=x.1.2 then [x.2] else []) :=
    congrComputes (ifComputes test
      (Holant.LocalDrafts.CountingHardness.RawGraphMachine.Access.list₁ unary i)
      (constantComputes (pairEncoding occurrenceEncoding unary) positionsEncoding []))
      (fun x => by simp)
  refine congrComputes ((W.tabulate occurrenceEncoding positionsEncoding (fun x => x.1.length)
    ((Wiring.firstComputes addressesEncoding encodingNatBool).andThen
      (W.lengthComputes encodingNatBool))
    (fun x i => if x.1.getD i 0=x.2 then [i] else []) cell).andThen (W.flatten unary)) ?_
  intro x
  change (List.range x.1.length).flatMap
    (fun i => if x.1.getD i 0=x.2 then [i] else [])=occurrences x.1 x.2
  unfold occurrences
  induction List.range x.1.length with
  | nil => rfl
  | cons i is ih =>
    by_cases h : x.1.getD i 0=x.2 <;>
      simp only [List.flatMap_cons,List.filter_cons,h,decide_true,decide_false,
        ite_true,ite_false,List.singleton_append,List.nil_append,ih,Bool.false_eq_true]

def withSentinel (bits : List Bool) : OriginalCoefficient.FirstTrue.Input :=
  ⟨bits++[true],by simp⟩

def sentinelComputes : Computes Frame.wordEncoding OriginalCoefficient.FirstTrue.inputEncoding withSentinel :=
  recode (joinComputes (identityComputes Frame.wordEncoding)
    (constantComputes Frame.wordEncoding Frame.wordEncoding [true])) id
    (fun _ => rfl) (fun _ => rfl)

theorem findIdx_sentinel (bits : List Bool) : (bits++[true]).findIdx id=bits.findIdx id := by
  induction bits with
  | nil => rfl
  | cons b bits ih => cases b <;> simp [List.findIdx_cons,ih]

def firstTrueComputes : Computes Frame.wordEncoding unary (fun bits => bits.findIdx id) :=
  congrComputes (sentinelComputes.andThen OriginalCoefficient.FirstTrue.computes) findIdx_sentinel

abbrev indexEncoding := pairEncoding positionsEncoding unary

def indexBits (x : List ℕ × ℕ) : List Bool := x.1.map (fun i => decide (i=x.2))

def indexBitsComputes : Computes indexEncoding Frame.wordEncoding indexBits := by
  let context := Wiring.firstComputes indexEncoding unary
  let xs := context.andThen (Wiring.firstComputes positionsEncoding unary)
  let wanted := context.andThen (Wiring.secondComputes positionsEncoding unary)
  let j := Wiring.secondComputes indexEncoding unary
  let found := (pairComputes xs j).andThen (W.getD unary 0)
  let test := (pairComputes (found.andThen UnaryBinary.computes)
    (wanted.andThen UnaryBinary.computes)).andThen Endpoints.equalComputes
  let byte : Computes (pairEncoding indexEncoding unary) Frame.wordEncoding
      (fun x => [decide (x.1.1.getD x.2 0=x.1.2)]) :=
    recode test id (fun _ => rfl) (fun _ => rfl)
  refine congrComputes (BinaryInterpolation.WeightCompiler.rangeWordsComputes indexEncoding
    (fun x => x.1.length) ((Wiring.firstComputes positionsEncoding unary).andThen
      (W.lengthComputes unary)) (fun x => [decide (x.1.1.getD x.2 0=x.1.2)]) byte) ?_
  intro x
  change (List.range x.1.length).flatMap (fun i => [decide (x.1.getD i 0=x.2)])=indexBits x
  rw [←List.map_eq_flatMap]
  apply List.ext_getElem
  · simp [indexBits]
  · intro i hi hj
    have hin : i<x.1.length := by simpa using hi
    simp [indexBits,List.getD_eq_getElem,hin]

theorem bits_index (x : List ℕ × ℕ) : (indexBits x).findIdx id=x.1.idxOf x.2 := by
  simp [indexBits,List.findIdx_map,List.idxOf,Bool.beq_eq_decide_eq]

def indexComputes : Computes indexEncoding unary (fun x => x.1.idxOf x.2) :=
  congrComputes (indexBitsComputes.andThen firstTrueComputes) bits_index

abbrev inputEncoding := pairEncoding addressesEncoding unary
def positions (x : List ℕ × ℕ) : List ℕ := occurrences x.1 (x.1.getD x.2 0)
def successorIndex (x : List ℕ × ℕ) : ℕ :=
  if (positions x).idxOf x.2+1<(positions x).length then (positions x).idxOf x.2+1 else 0
def next (x : List ℕ × ℕ) : ℕ := (positions x).getD (successorIndex x) 0

def positionsComputes : Computes inputEncoding positionsEncoding positions :=
  (pairComputes (Wiring.firstComputes addressesEncoding unary) (W.getD encodingNatBool 0)).andThen
    occurrencesComputes

def successorIndexComputes : Computes inputEncoding unary successorIndex := by
  let rank := ((pairComputes positionsComputes (Wiring.secondComputes addressesEncoding unary)).andThen
    indexComputes).andThen W.succComputes
  let len := positionsComputes.andThen (W.lengthComputes unary)
  let test := (pairComputes (rank.andThen UnaryBinary.computes)
    (len.andThen UnaryBinary.computes)).andThen Endpoints.lessComputes
  exact congrComputes (ifComputes test rank (constantComputes inputEncoding unary 0))
    (fun x => by simp [successorIndex])

def nextComputes : Computes inputEncoding unary next :=
  (pairComputes positionsComputes successorIndexComputes).andThen (W.getD unary 0)

def successors (addresses : List ℕ) : List ℕ :=
  (List.range addresses.length).map (fun i => next (addresses,i))

def successorsComputes : Computes addressesEncoding positionsEncoding successors :=
  W.tabulate addressesEncoding unary List.length (W.lengthComputes encodingNatBool)
    (fun addresses i => next (addresses,i)) nextComputes

/-- On every real occurrence, the finite conditional is exactly cyclic
successor modulo the occurrence count. Empty lists never supply a real index. -/
theorem next_eq (addresses : List ℕ) (current : ℕ) (hi : current<addresses.length) :
    next (addresses,current)=
      let ps := occurrences addresses (addresses.getD current 0)
      ps.getD ((ps.idxOf current+1)%ps.length) current := by
  let ps := occurrences addresses (addresses.getD current 0)
  have hm : current∈ps := by simp [ps,occurrences,hi]
  have hr : ps.idxOf current<ps.length := List.idxOf_lt_length_iff.mpr hm
  have hp : 0<ps.length := by omega
  have he : (if ps.idxOf current+1<ps.length then ps.idxOf current+1 else 0)=
      (ps.idxOf current+1)%ps.length := by
    by_cases h : ps.idxOf current+1<ps.length
    · simp [h,Nat.mod_eq_of_lt h]
    · have eq : ps.idxOf current+1=ps.length := by omega
      simp [h,eq]
  change ps.getD (if ps.idxOf current+1<ps.length then ps.idxOf current+1 else 0) 0=_
  rw [he]
  rw [List.getD_eq_getElem _ _ (Nat.mod_lt _ hp),
    List.getD_eq_getElem _ _ (Nat.mod_lt _ hp)]

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryCSPProgrammeScan
