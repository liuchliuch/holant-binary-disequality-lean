import Holant.Proofs.BinaryInterpolation.FiniteSupportMachine.Semantics


namespace Holant.LocalDrafts.BinaryInterpolation.FiniteSupportMachine.Controller

open Computability Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open FixedGadgetSubstitution.Compiler UniversalPairReduction.SmoothingCompiler
open Holant.OneHot.StackProgram.GraphLabelEncoding
open Holant.LocalDrafts.Tractability.AffineMachine
open EncodedTable (bitsEncoding rowEncoding)

abbrev Frames := List BackSubstitution.FrameData
def framesEncoding := framedListEncoding BackSubstitution.frameEncoding
def flagsEncoding := pairEncoding encodingBoolBool encodingBoolBool
abbrev State := (Bool × Bool) × (Codec.Matrix × (Frames × List Bool))
def bodyEncoding := pairEncoding Codec.encoding (pairEncoding framesEncoding bitsEncoding)
def encoding := pairEncoding flagsEncoding bodyEncoding
def outputEncoding := optionEncoding bitsEncoding

def initial (d : Codec.Matrix) : State := ((true, false), Codec.normalize d, [], [])
def pivotContext (s : State) : Elimination.Context := (s.2.1, (Elimination.selected s.2.1).2)
def pivot (s : State) : State :=
  (s.1, Elimination.update (pivotContext s), Elimination.save (pivotContext s) :: s.2.2.1, s.2.2.2)
def free (s : State) : State :=
  ((false, false), s.2.1, s.2.2.1, List.replicate s.2.1.1 false)
def failed (s : State) : State := ((false, true), s.2)
def tail (fs : Frames) : Frames :=
  (List.range (fs.length - 1)).map (fun j => fs.getD (j + 1) (0, 0, false, []))
def back (s : State) : State :=
  (s.1, s.2.1, tail s.2.2.1,
    BackSubstitution.value (s.2.2.1.getD 0 (0, 0, false, []), s.2.2.2))
def step (s : State) : State :=
  if s.1.2 then s else
    if s.1.1 then
      if Elimination.bad s.2.1 then failed s else
        if (Elimination.selected s.2.1).1 then pivot s else free s
    else if s.2.2.1.length = 0 then s else back s
def answer (s : State) : Option (List Bool) := if s.1.2 then none else some s.2.2.2
def Terminal (s : State) : Prop := s.1.2 = true ∨ (s.1.1 = false ∧ s.2.2.1 = [])

noncomputable def flags : Computes encoding flagsEncoding Prod.fst := Wiring.firstComputes _ _
noncomputable def body : Computes encoding bodyEncoding Prod.snd := Wiring.secondComputes _ _
noncomputable def forward := flags.andThen (Wiring.firstComputes _ _)
noncomputable def failure := flags.andThen (Wiring.secondComputes _ _)
noncomputable def matrix := body.andThen (Wiring.firstComputes _ _)
noncomputable def rest := body.andThen (Wiring.secondComputes _ _)
noncomputable def frames := rest.andThen (Wiring.firstComputes _ _)
noncomputable def word := rest.andThen (Wiring.secondComputes _ _)

noncomputable def initialComputes : Computes Codec.encoding encoding initial :=
  pairComputes (constantComputes Codec.encoding flagsEncoding (true, false))
    (pairComputes Codec.normalizeComputes
      (constantComputes Codec.encoding (pairEncoding framesEncoding bitsEncoding) ([], [])))

noncomputable def pivotContextComputes : Computes encoding Elimination.contextEncoding pivotContext :=
  pairComputes matrix ((matrix.andThen Elimination.selectedComputes).andThen
    (Wiring.secondComputes encodingBoolBool
      (pairEncoding UnaryBinary.unaryEncoding UnaryBinary.unaryEncoding)))

noncomputable def pivotComputes : Computes encoding encoding pivot := by
  let saved := pivotContextComputes.andThen Elimination.saveComputes
  let singleton := fixedListComputes encoding BackSubstitution.frameEncoding
    (fun s (_ : Unit) => Elimination.save (pivotContext s)) (fun _ => saved) [()]
  let pushed := (pairComputes singleton frames).andThen (WireLists.append BackSubstitution.frameEncoding)
  exact congrComputes (pairComputes flags
    (pairComputes (pivotContextComputes.andThen Elimination.updateComputes) (pairComputes pushed word)))
      (fun _ => rfl)

noncomputable def freeComputes : Computes encoding encoding free :=
  pairComputes (constantComputes encoding flagsEncoding (false, false))
    (pairComputes matrix (pairComputes frames
      ((matrix.andThen Codec.dimension).andThen (WireLists.replicate encodingBoolBool false))))
noncomputable def failedComputes : Computes encoding encoding failed :=
  pairComputes (constantComputes encoding flagsEncoding (false, true)) body

noncomputable def tailComputes : Computes framesEncoding framesEncoding tail := by
  let old := Wiring.firstComputes framesEncoding UnaryBinary.unaryEncoding
  let j := (Wiring.secondComputes framesEncoding UnaryBinary.unaryEncoding).andThen WireLists.succComputes
  exact WireLists.tabulate framesEncoding BackSubstitution.frameEncoding (fun fs => fs.length - 1)
    ((WireLists.lengthComputes BackSubstitution.frameEncoding).andThen Endpoints.unaryPredecessorComputes)
    _ (AccessPrograms.get BackSubstitution.frameEncoding (0, 0, false, []) old j)

noncomputable def backComputes : Computes encoding encoding back := by
  let head := frames.andThen (getDComputes BackSubstitution.frameEncoding 0 (0, 0, false, []))
  exact pairComputes flags (pairComputes matrix
    (pairComputes (frames.andThen tailComputes)
      ((pairComputes head word).andThen BackSubstitution.computes)))

noncomputable def computes : Computes encoding encoding step := by
  let id := identityComputes encoding
  let isEmpty := (pairComputes (frames.andThen (WireLists.lengthComputes BackSubstitution.frameEncoding))
    (constantComputes encoding UnaryBinary.unaryEncoding 0)).andThen (equalComputes UnaryBinary.unaryEncoding)
  let hasPivot := (matrix.andThen Elimination.selectedComputes).andThen
    (Wiring.firstComputes encodingBoolBool
      (pairEncoding UnaryBinary.unaryEncoding UnaryBinary.unaryEncoding))
  apply congrComputes (ifComputes failure id (ifComputes forward
    (ifComputes (matrix.andThen Elimination.badComputes) failedComputes
      (ifComputes hasPivot pivotComputes freeComputes))
    (ifComputes isEmpty id backComputes)))
  intro s
  simp [step, isEmpty, id, hasPivot, Function.comp_def]

noncomputable def answerComputes : Computes encoding outputEncoding answer := by
  let present : Computes encoding outputEncoding (fun s => some s.2.2.2) :=
    recode (joinComputes (constantComputes encoding Frame.wordEncoding [true])
      (word.andThen (encodeComputes bitsEncoding))) id (fun _ => rfl) (fun _ => rfl)
  exact ifComputes failure (constantComputes encoding outputEncoding none) present

@[simp] theorem tail_nil : tail [] = [] := rfl
@[simp] theorem tail_cons (f : BackSubstitution.FrameData) (fs : Frames) : tail (f :: fs) = fs := by
  simp only [tail, List.length_cons, Nat.add_sub_cancel]
  rw [DensePrograms.range_map]
  simpa [List.getD_eq_getElem] using List.ofFn_get fs
@[simp] theorem tail_length (fs : Frames) : (tail fs).length = fs.length - 1 := by simp [tail]

theorem stable (s : State) (h : Terminal s) : step s = s := by
  rcases h with hf | ⟨hf, hs⟩
  · simp [step, hf]
  · simp [step, hf, hs]

def measure (s : State) : ℕ :=
  if s.1.2 then 0 else if s.1.1 then 2 * s.2.1.1 + s.2.2.1.length + 1 else s.2.2.1.length

theorem measure_zero (s : State) : measure s = 0 ↔ Terminal s := by
  cases hf : s.1.2 <;> cases hd : s.1.1 <;> simp [measure, Terminal, hf, hd]

theorem measure_step (s : State) : measure (step s) ≤ measure s - 1 := by
  cases hf : s.1.2 with
  | true => simp [step, measure, hf]
  | false =>
    cases hd : s.1.1 with
    | true =>
      cases hb : Elimination.bad s.2.1 with
      | true => simp [step, measure, hf, hd, hb, failed]
      | false =>
        cases hp : (Elimination.selected s.2.1).1 with
        | false => simp [step, measure, hf, hd, hb, hp, free]
        | true =>
          have hn := (PivotPrograms.selected_valid (Codec.lift s.2.1) hp).2.1
          simp only [Codec.lift] at hn
          simp only [step, hf, hd, hb, hp, Bool.false_eq_true, Bool.coe_true,
            if_false, if_true, pivot, measure, Elimination.dimension_update,
            pivotContext, List.length_cons]
          omega
    | false =>
      by_cases he : s.2.2.1.length = 0
      · simp [step, measure, hf, hd, he]
      · simp [step, measure, hf, hd, he, back]

theorem measure_iterate (s : State) (k : ℕ) : measure ((step^[k]) s) ≤ measure s - k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have h := measure_step ((step^[k]) s)
    omega

theorem terminal_iterate (s : State) (k : ℕ) (hk : measure s ≤ k) : Terminal ((step^[k]) s) := by
  apply (measure_zero _).mp
  have h := measure_iterate s k
  omega

theorem primitive_bound (s : State) :
    primitiveCost computes.machine (computes.outputs s).steps
      (some (Turing.initList computes.machine.computer (encoding.encode s))) ≤
        (primitivePolynomial computes).eval (encoding.encode s).length :=
  computes_primitive_cost computes s

end Holant.LocalDrafts.BinaryInterpolation.FiniteSupportMachine.Controller
