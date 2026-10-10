import Holant.Proofs.Reductions.SingleWeightCompletion.ComponentCharge
import Holant.Proofs.Reductions.RootPreprocessing.Programs
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.OriginalWordTableRun


noncomputable section
namespace Holant.LocalDrafts.Hardness.SingleWeightCompletion.ChargeProgram
open Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open GraphPreprocessing GraphPreprocessing.OriginalCoefficient
open FixedGadgetSubstitution.Compiler RawClosedNetwork
open UniversalPairReduction.SmoothingCompiler
open Holant.OneHot.StackProgram.GraphLabelEncoding
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {s : ℕ} {a : ℕ → ℕ}

abbrev Probe := Σ x : Query s 1 a, Fin x.1.val.vertices.length
def probeEncoding := sigmaEncoding (queryEncoding s 1 a)
  (fun x => OccurrenceLabel.unaryPortEncoding x.1.val.vertices.length)
def probesEncoding := ContextFlatMap.inputEncoding (queryEncoding s 1 a)
  (fun x => OccurrenceLabel.unaryPortEncoding x.1.val.vertices.length)
def candidate (p : Probe (s:=s) (a:=a)) : Query s 1 a := ⟨p.1.1,p.2⟩
def outerComputes : Computes (probeEncoding (s:=s) (a:=a)) (queryEncoding s 1 a) (fun p => p.1) :=
  recode (Wiring.firstComputes (queryEncoding s 1 a) UnaryBinary.unaryEncoding)
    (fun p => (p.1,p.2.val)) (fun _ => rfl) (fun _ => rfl)
def candidateComputes : Computes (probeEncoding (s:=s) (a:=a)) (queryEncoding s 1 a) candidate := by
  let idx : Computes (probeEncoding (s:=s) (a:=a)) UnaryBinary.unaryEncoding (fun p => p.2.val) :=
    recode (Wiring.secondComputes (queryEncoding s 1 a) UnaryBinary.unaryEncoding)
      (fun p => (p.1,p.2.val)) (fun _ => rfl) (fun _ => rfl)
  exact recode (pairComputes (outerComputes.andThen (sourceComputes s 1 a)) idx)
    id (fun _ => rfl) (fun _ => rfl)
def labelComputes : Computes (queryEncoding s 1 a) UnaryBinary.unaryEncoding
    (fun x => component x.1 x.2) := RawComponentLabel.computes s 1 a
def sameComputes : Computes (probeEncoding (s:=s) (a:=a)) encodingBoolBool
    (fun p => decide (component p.1.1 p.2 = component p.1.1 p.1.2)) :=
  (pairComputes (candidateComputes.andThen labelComputes) (outerComputes.andThen labelComputes)).andThen
    (equalComputes UnaryBinary.unaryEncoding)
def probesComputes : Computes (queryEncoding s 1 a) (probesEncoding (s:=s) (a:=a))
    (fun x => ⟨x,List.finRange x.1.val.vertices.length⟩) :=
  recode (pairComputes (identityComputes (queryEncoding s 1 a))
    (((sourceComputes s 1 a).andThen (vertexCountComputes s 1 a)).andThen ComponentSelection.UnaryRange.computes))
    id (fun _ => rfl) (fun x => by
      change frame _ ++ framedListEncode UnaryBinary.unaryEncoding (List.range _) = _
      rw [←finRange_values,finListEncoding]
      rfl)

def count (w : ℕ → ℕ) (x : Query s 1 a) : ℕ :=
  ((List.finRange x.1.val.vertices.length).map fun v =>
    if component x.1 v=component x.1 x.2 then w (x.1.val.vertices.get v).1 else 0).sum
def tokens (w : ℕ → ℕ) (p : Probe (s:=s) (a:=a)) : List Bool :=
  if component p.1.1 p.2=component p.1.1 p.1.2
  then List.replicate (w (p.1.1.val.vertices.get p.2).1) true else []
def tokensComputes (w : ℕ → ℕ) : Computes (probeEncoding (s:=s) (a:=a)) Frame.wordEncoding (tokens w) := by
  let yes := (candidateComputes.andThen (weightComputes s 1 a w)).andThen (encodeComputes UnaryBinary.unaryEncoding)
  exact congrComputes (ifComputes sameComputes yes (constantComputes _ Frame.wordEncoding []))
    (fun p => by simp [tokens,candidate,UnaryBinary.unaryEncoding])
def countComputes (w : ℕ → ℕ) : Computes (queryEncoding s 1 a) UnaryBinary.unaryEncoding (count w) := by
  let run := probesComputes.andThen
    (ContextFlatMap.computes (queryEncoding s 1 a)
      (fun x => OccurrenceLabel.unaryPortEncoding x.1.val.vertices.length) (tokens w) (tokensComputes w))
  refine recode run id (fun _ => rfl) ?_
  intro x
  change (List.finRange _).flatMap (fun v => tokens w ⟨x,v⟩) = List.replicate (count w x) true
  have ht (v : Fin x.1.val.vertices.length) : tokens w ⟨x,v⟩ =
      List.replicate (if component x.1 v=component x.1 x.2 then w (x.1.val.vertices.get v).1 else 0) true := by
    by_cases h : component x.1 v=component x.1 x.2 <;> simp [tokens,h]
  simp only [ht,flatMap_tokens,count]

def zeroWeight (d : Fin s → ℕ) (j : ℕ) : ℕ :=
  if hj : j < s then if pin (a j) (d ⟨j,hj⟩) then 0 else extra (a j) (d ⟨j,hj⟩) else 0
def oneWeight (d : Fin s → ℕ) (j : ℕ) : ℕ :=
  if hj : j < s then if pin (a j) (d ⟨j,hj⟩) then extra (a j) (d ⟨j,hj⟩) else 0 else 0
theorem weights_charge (d : Fin s → ℕ) (i : Fin s) :
    (zeroWeight (a:=a) d i.val:ℤ) - oneWeight (a:=a) d i.val = 2*(d i:ℤ)-a i.val := by
  rw [charge_extra]
  simp only [zeroWeight,oneWeight,dif_pos i.isLt]
  cases pin (a i.val) (d i) <;> simp
theorem count_charge (d : Fin s → ℕ) (x : Query s 1 a) :
    (count (zeroWeight (a:=a) d) x:ℤ) - count (oneWeight (a:=a) d) x = componentCharge d x.1 (component x.1 x.2) := by
  simp only [count,componentCharge,←List.ofFn_eq_map,List.sum_ofFn,Nat.cast_sum,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro v _
  by_cases h : component x.1 v=component x.1 x.2
  · simpa [h,chargeAt,RawClosedNetwork.signatureLabel] using
      weights_charge d (x.1.val.signatureLabel x.1.property v)
  · simp [h]

def balancedRowComputes (d : Fin s → ℕ) : Computes (queryEncoding s 1 a) encodingBoolBool
    (fun x => decide (componentCharge d x.1 (component x.1 x.2)=0)) := by
  let counts : Computes (queryEncoding s 1 a)
      (pairEncoding UnaryBinary.unaryEncoding UnaryBinary.unaryEncoding)
      (fun x => (count (zeroWeight (a:=a) d) x,count (oneWeight (a:=a) d) x)) :=
    pairComputes (countComputes (s:=s) (a:=a) (zeroWeight (a:=a) d))
      (countComputes (s:=s) (a:=a) (oneWeight (a:=a) d))
  let run := counts.andThen (equalComputes UnaryBinary.unaryEncoding)
  refine congrComputes run ?_
  intro x
  have he := count_charge d x
  dsimp only [Function.comp_apply]
  apply decide_eq_decide.mpr
  omega
def badCount (d : Fin s → ℕ) (r : Input (s:=s) (a:=a)) : ℕ :=
  ((List.finRange r.val.vertices.length).map fun v => if componentCharge d r (component r v)=0 then 0 else 1).sum
def badCountComputes (d : Fin s → ℕ) : Computes (validatedEncoding s 1 a) UnaryBinary.unaryEncoding (badCount d) := by
  let one : Computes (queryEncoding s 1 a) Frame.wordEncoding
      (fun x => if decide (componentCharge d x.1 (component x.1 x.2)=0)
        then [] else [true]) :=
    ifComputes (balancedRowComputes (s:=s) (a:=a) d)
      (constantComputes (queryEncoding s 1 a) Frame.wordEncoding [])
      (constantComputes (queryEncoding s 1 a) Frame.wordEncoding [true])
  let run := allRowsFlatMapComputes s 1 a _ one
  refine recode run id (fun _ => rfl) ?_
  intro r
  change (List.finRange _).flatMap _ = List.replicate (badCount d r) true
  have he (v : Fin r.val.vertices.length) :
      (if decide (componentCharge d r (component r v)=0) then ([]:List Bool) else [true]) =
        List.replicate (if componentCharge d r (component r v)=0 then 0 else 1) true := by
    by_cases h : componentCharge d r (component r v)=0 <;> simp [h]
  simp only [id_eq,he,flatMap_tokens,badCount]
theorem badCount_zero (d : Fin s → ℕ) (r : Input (s:=s) (a:=a)) : badCount d r=0 ↔ Balanced d r := by
  simp [badCount,←List.ofFn_eq_map,List.sum_ofFn,Finset.sum_eq_zero_iff,Balanced]
def balancedComputes (d : Fin s → ℕ) : Computes (validatedEncoding s 1 a) encodingBoolBool
    (fun r => decide (Balanced d r)) :=
  congrComputes ((pairComputes (badCountComputes (s:=s) (a:=a) d)
    (constantComputes (validatedEncoding s 1 a) UnaryBinary.unaryEncoding 0)).andThen
      (equalComputes UnaryBinary.unaryEncoding))
    (fun r => by
      dsimp only [Function.comp_apply]
      exact decide_eq_decide.mpr (badCount_zero d r))

end Holant.LocalDrafts.Hardness.SingleWeightCompletion.ChargeProgram
