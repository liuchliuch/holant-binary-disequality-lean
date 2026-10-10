import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.SingletonStages

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.SingletonLabel
open Turing Computability StackProtocol BinaryCompose
open Turing.TM2.Stmt
open Holant.OneHot.StackProgram Holant.OneHot.StackProgram.GraphLabelEncoding
variable (s b : ℕ) (arity : ℕ → ℕ) (framed : Bool)
set_option backward.isDefEq.respectTransparency false

/-- Structural compilation of fixed output bits, with no whole-word runtime operation. -/
theorem embed_word (word : List Bool) (next : TM2.Stmt (fun _ : Unit => Bool) (RecodeLabel s arity) (Option Bool × Unit))
    (stop : Option (Label s arity)) :
    embedStmt (literalLayout (fun _ => [])) Returning.state (literalLabel s arity) stop
      (FixedFieldMachines.Constant.pushWord () word next) =
    FixedFieldMachines.Constant.pushWord literalKey word
      (embedStmt (literalLayout (fun _ => [])) Returning.state (literalLabel s arity) stop next) := by
  induction word generalizing next with
  | nil => rfl
  | cons bit word ih =>
    rw [FixedFieldMachines.Constant.pushWord, ih]
    rfl

/-- The actual fixed-family decoder reads the extracted original signature ID. -/
theorem recode (i : Fin s) (p : Fin (arity i.val)) (raw query output : List Bool) :
    RunsExactly (machine s b arity framed).computer.step
      (cfg (literalLabel s arity (.inl false)) ()
        (work raw query (List.replicate p.val true) [] (Holant.Algebraic.frame (encodeNat i.val) ++ (true :: List.replicate p.val true)) [] output))
      (cfg (phase s arity 4) ()
        (work raw query (List.replicate p.val true) [] ((treeLabelEncoding s b arity).encode (OccurrenceLabel.literal ⟨i, some p⟩)) [] output)) 2 := by
  let a : OccurrenceLabel.Input s arity := ⟨i, some p⟩
  let layout := literalLayout (work raw query (List.replicate p.val true) [] [] [] output)
  have decoded := FiniteRecode.decode_step (OccurrenceLabel.inputEncoding s arity)
    (treeLabelEncoding s b arity) OccurrenceLabel.literal (OccurrenceLabel.inputBound s arity) a
    (OccurrenceLabel.input_length_le s arity a)
  have h := Traversal.CallExits.active_run_frame (literalLayout (fun _ => [])) layout rfl Returning.state
    (literalLabel s arity) (literalReturn s arity) (recoder s b arity).program
    (program s b arity framed) (fun _ => rfl) _ _ _ (runsExactly_one decoded) rfl
  have first : RunsExactly (machine s b arity framed).computer.step
      (cfg (literalLabel s arity (.inl false)) ()
        (work raw query (List.replicate p.val true) [] (Holant.Algebraic.frame (encodeNat i.val) ++ (true :: List.replicate p.val true)) [] output))
      (cfg (literalLabel s arity (.inr a)) () (work raw query (List.replicate p.val true) [] [] [] output)) 1 := by
    rw [BinaryCompose.Machine.init_eq] at h
    simpa only [embedCfg, Option.elim_some, Returning.state, id_eq, layout, literal_work,
      recoder, FiniteRecode.machine, OccurrenceLabel.encode_singleton, a, cfg, RunsExactly, machine, FinTM2.step] using h
  let word := (treeLabelEncoding s b arity).encode (OccurrenceLabel.literal a)
  have second : (machine s b arity framed).computer.step
      (cfg (literalLabel s arity (.inr a)) () (work raw query (List.replicate p.val true) [] [] [] output)) =
      some (cfg (phase s arity 4) () (work raw query (List.replicate p.val true) [] word [] output)) := by
    change some (TM2.stepAux
      (embedStmt (literalLayout (fun _ => [])) Returning.state (literalLabel s arity) (some (phase s arity 4))
        (FixedFieldMachines.Constant.pushWord () word .halt)) (none, ()) _) = _
    rw [embed_word, FixedFieldMachines.Constant.pushWord_eval]
    change some (cfg (phase s arity 4) () (Function.update (work raw query (List.replicate p.val true) [] [] [] output) literalKey (word ++ []))) = _
    simp only [List.append_nil]
    congr 2
    funext key; cases key with
    | inl key => cases key with
      | inl k => fin_cases k <;> rfl
      | inr k => fin_cases k <;> rfl
    | inr u => fin_cases u <;> rfl
  exact first.trans (runsExactly_one second)

def emitTicks (framed : Bool) (word : List Bool) : ℕ := 2 * word.length + if framed then 3 else 2

/-- Emit the exact label or its tree-prefix frame, preserving the caller suffix. -/
theorem emit (raw query port word output : List Bool) :
    RunsExactly (machine s b arity framed).computer.step
      (cfg (phase s arity 4) () (work raw query port [] word [] output))
      (cfg (phase s arity 7) () (work raw query port [] [] [] (outputWord framed word ++ output)))
      (emitTicks framed word) := by
  cases framed with
  | false =>
    have h := Machine.StackWord.move_exact literalKey outputKey temporaryKey
      (by decide) (by decide) (by decide) (machine s b arity false).computer.step
      (phase s arity 4) (phase s arity 5) (phase s arity 7)
      (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl)
      () (work raw query port [] [] [] []) word output
    convert h using 1 <;> try { simp only [emitTicks, outputWord, Bool.false_eq_true, ↓reduceIte]; omega }
    all_goals dsimp [cfg]; congr 1; funext key; cases key with
      | inl key => cases key with
        | inl k => fin_cases k <;> rfl
        | inr k => fin_cases k <;> rfl
      | inr u => fin_cases u <;> rfl
  | true =>
    have h := FixedFieldMachines.FrameEmit.prepend_exact literalKey outputKey temporaryKey
      (by decide) (by decide) (by decide) (machine s b arity true).computer.step
      (phase s arity 4) (phase s arity 5) (phase s arity 6) (phase s arity 7)
      (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl)
      () (work raw query port [] [] [] []) word output
    convert h using 1 <;> try { simp only [emitTicks, outputWord, ↓reduceIte] }
    all_goals dsimp [cfg]; congr 1; funext key; cases key with
      | inl key => cases key with
        | inl k => fin_cases k <;> rfl
        | inr k => fin_cases k <;> rfl
      | inr u => fin_cases u <;> rfl

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.SingletonLabel
