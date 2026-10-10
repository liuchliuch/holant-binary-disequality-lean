import Holant.Proofs.Tractability.ProductMachine.Rewrite


set_option backward.isDefEq.respectTransparency false

namespace Holant.LocalDrafts.Tractability.ProductMachine.PivotScan

open Computability Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open GraphPreprocessing.OriginalCoefficient
open FixedGadgetSubstitution.Compiler UniversalPairReduction.SmoothingCompiler
open Holant.OneHot.StackProgram.GraphLabelEncoding
open Templates (Record recordEncoding)

def eligible (r : Record) : Bool := (r.1 == 2) && Bool.xor (r.2.1 == 0) (r.2.2.1 == 0)
def candidate (r : Record) : Rewrite.Pivot :=
  (if r.2.1 = 0 then r.2.2.1 else r.2.1, r.2.2.2.1 != 0)
def candidates (fs : List Record) : List Rewrite.Pivot := (fs.filter eligible).map candidate
def selected (fs : List Record) : Rewrite.Pivot := (candidates fs).getD 0 (0, false)

noncomputable def equal (i : Fin 5) (n : ℕ) :
    Computes recordEncoding encodingBoolBool (fun r => decide (Rewrite.get r i = n)) :=
  (pairComputes (Rewrite.getComputes i)
    (constantComputes recordEncoding encodingNatBool n)).andThen Endpoints.equalComputes

noncomputable def eligibleComputes : Computes recordEncoding encodingBoolBool eligible :=
  congrComputes ((pairComputes (equal 0 2)
    ((pairComputes (equal 1 0) (equal 2 0)).andThen
      (Rewrite.boolPairComputes (fun p => Bool.xor p.1 p.2)))).andThen
    (Rewrite.boolPairComputes (fun p => p.1 && p.2)))
    (fun r => by simp [eligible, Rewrite.get, Bool.beq_eq_decide_eq])

noncomputable def candidateComputes : Computes recordEncoding Rewrite.pivotEncoding candidate :=
  recode (pairComputes
    (ifComputes (equal 1 0) (Rewrite.getComputes 2) (Rewrite.getComputes 1))
    ((equal 3 0).andThen Rewrite.negComputes)) id (fun _ => rfl)
    (fun r => by simp [candidate, Rewrite.get, Rewrite.pivotEncoding, pairEncoding, RawClosedNetwork.endpointEncoding, framedProductEncoding, bne, Bool.beq_eq_decide_eq])

def chunk (r : Record) : List Bool :=
  if eligible r then entry Rewrite.pivotEncoding (candidate r) else []

noncomputable def chunkComputes : Computes recordEncoding Frame.wordEncoding chunk :=
  ifComputes eligibleComputes (candidateComputes.andThen (entryComputes Rewrite.pivotEncoding))
    (constantComputes recordEncoding Frame.wordEncoding [])

theorem chunks (fs : List Record) : fs.flatMap chunk = entries Rewrite.pivotEncoding (candidates fs) := by
  induction fs with
  | nil => rfl
  | cons f fs ih => cases h : eligible f <;> simp [chunk, candidates, entries, h, ih]

noncomputable def candidatesComputes :
    Computes (framedListEncoding recordEncoding) (framedListEncoding Rewrite.pivotEncoding) candidates := by
  let prepare : Computes (framedListEncoding recordEncoding)
      (ContextFlatMap.inputEncoding Frame.wordEncoding (fun _ => recordEncoding))
      (fun fs => (⟨[], fs⟩ : Σ _ : List Bool, List Record)) :=
    recode (pairComputes (constantComputes (framedListEncoding recordEncoding) Frame.wordEncoding [])
      (identityComputes (framedListEncoding recordEncoding))) id (fun _ => rfl) (fun _ => rfl)
  let worker : Computes (sigmaEncoding Frame.wordEncoding (fun _ => recordEncoding))
      Frame.wordEncoding (fun x => chunk x.2) :=
    recode ((Wiring.secondComputes Frame.wordEncoding recordEncoding).andThen chunkComputes)
      (fun x => (x.1, x.2)) (fun _ => rfl) (fun _ => rfl)
  let body := prepare.andThen (ContextFlatMap.computes Frame.wordEncoding (fun _ => recordEncoding) _ worker)
  refine recode (joinComputes body
    (constantComputes (framedListEncoding recordEncoding) Frame.wordEncoding [false]))
    id (fun _ => rfl) ?_
  intro fs
  change fs.flatMap chunk ++ [false] = _
  rw [chunks]
  simpa only [framedListEncoding, framedListEncode, List.append_nil] using
    entries_append_encode Rewrite.pivotEncoding (candidates fs) []

noncomputable def computes : Computes (framedListEncoding recordEncoding) Rewrite.pivotEncoding selected :=
  candidatesComputes.andThen (getDComputes Rewrite.pivotEncoding 0 (0, false))

theorem candidate_positive (r : Record) (h : eligible r = true) : 0 < (candidate r).1 := by
  by_cases hl : r.2.1 = 0 <;> by_cases hr : r.2.2.1 = 0 <;>
    simp_all [eligible, candidate] <;> omega

theorem sentinel_iff (fs : List Record) : (selected fs).1 = 0 ↔ candidates fs = [] := by
  have hp (p : Rewrite.Pivot) (h : p ∈ candidates fs) : 0 < p.1 := by
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp h
    exact candidate_positive r (List.mem_filter.mp hr).2
  cases hs : candidates fs with
  | nil => simp [selected, hs]
  | cons p ps =>
    have h := hp p (by simp [hs])
    simp [selected, hs, Nat.ne_of_gt h]

theorem primitive_bound (fs : List Record) :
    primitiveCost computes.machine (computes.outputs fs).steps
      (some (Turing.initList computes.machine.computer ((framedListEncoding recordEncoding).encode fs))) ≤
      (primitivePolynomial computes).eval ((framedListEncoding recordEncoding).encode fs).length :=
  computes_primitive_cost computes fs

end Holant.LocalDrafts.Tractability.ProductMachine.PivotScan
