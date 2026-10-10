import Holant.OneHot.StackProgram.GraphCodeMachine.Syntax

/-! Exact operational stages for fixed literal actions and bounded label parsing. -/
namespace Holant.OneHot.StackProgram.GraphCodeMachine
open Turing Computability Holant.Complexity StackProtocol
variable {A : Type} [Fintype A] (e : Encoding A Bool) (C : ℕ) (entry : Action A)
set_option backward.isDefEq.respectTransparency false

def active (input : List Bool) (pending : List (Action A)) (output : List Bool) : Config A :=
  cfg (.fixed 1) () (tapes input ((workEncoding e).encode pending) output [] [] [])

theorem schedule_exact (label : Label A) (tasks pending : List (Action A)) (input output : List Bool)
    (hp : (machine e C entry).program label = schedule e tasks) :
    (machine e C entry).computer.step (cfg label () (tapes input ((workEncoding e).encode pending) output [] [] [])) =
      some (active e input (tasks ++ pending) output) := by
  change some (TM2.stepAux ((machine e C entry).program label) (none, ()) _) = _
  rw [hp]
  unfold schedule
  rw [FixedFieldMachines.Constant.pushWord_eval]
  simp only [TM2.stepAux, active, cfg, work_prepend]
  congr 2; funext k; fin_cases k <;> rfl

theorem emit_exact (label : Label A) (code : Code A) (pending : List (Action A)) (input output : List Bool)
    (hp : (machine e C entry).program label = emitCode e code) :
    (machine e C entry).computer.step (cfg label () (tapes input ((workEncoding e).encode pending) output [] [] [])) =
      some (active e input pending ((records (opEncoding e) code).reverse ++ output)) := by
  change some (TM2.stepAux ((machine e C entry).program label) (none, ()) _) = _
  rw [hp]
  unfold emitCode
  rw [FixedFieldMachines.Constant.pushWord_eval]
  simp only [TM2.stepAux, active, cfg]
  congr 2; funext k; fin_cases k <;> rfl

theorem read_label (scan restore decode : Label A) (next : A → Label A)
    (hs : (machine e C entry).program scan = GraphPreprocessing.Frame.scanStmt 0 5 scan restore (.fixed 18))
    (hr : (machine e C entry).program restore = copyMoveStmt 5 4 restore decode)
    (hd : (machine e C entry).program decode = labelStmt e C next)
    (a : A) (ha : (e.encode a).length ≤ C) (suffix : List Bool) (pending : List (Action A)) (output : List Bool) :
    RunsExactly (machine e C entry).computer.step
      (cfg scan () (tapes (Holant.Algebraic.frame (e.encode a) ++ suffix) ((workEncoding e).encode pending) output [] [] []))
      (cfg (next a) () (tapes suffix ((workEncoding e).encode pending) output [] [] []))
      (2 * (e.encode a).length + 3) := by
  have h := GraphPreprocessing.Frame.extract_exact (0 : Fin 6) 4 5
    (by decide) (by decide) (by decide) (machine e C entry).computer.step scan restore decode (.fixed 18)
    (executesAt_tm2 _ _ _ hs) (executesAt_tm2 _ _ _ hr) ()
    (tapes [] ((workEncoding e).encode pending) output [] [] []) (e.encode a) suffix []
  have before : tapes3 (tapes [] ((workEncoding e).encode pending) output [] [] []) (0 : Fin 6) 4 5
      (Holant.Algebraic.frame (e.encode a) ++ suffix) [] [] =
      tapes (Holant.Algebraic.frame (e.encode a) ++ suffix) ((workEncoding e).encode pending) output [] [] [] := by
    funext k; fin_cases k <;> rfl
  have after : tapes3 (tapes [] ((workEncoding e).encode pending) output [] [] []) (0 : Fin 6) 4 5
      suffix (e.encode a ++ []) [] = tapes suffix ((workEncoding e).encode pending) output [] (e.encode a) [] := by
    simp only [List.append_nil]
    funext k; fin_cases k <;> rfl
  rw [before, after] at h
  have done : (machine e C entry).computer.step
      (cfg decode () (tapes suffix ((workEncoding e).encode pending) output [] (e.encode a) [])) =
      some (cfg (next a) () (tapes suffix ((workEncoding e).encode pending) output [] [] [])) := by
    change some (TM2.stepAux ((machine e C entry).program decode) (none, ()) _) = _
    rw [hd]
    have hh := Machine.Dispatch.decodeStmt_exact (4 : Fin 6)
      (fun bits => (e.decode bits).elim (.fixed 18) next) (.fixed 18) C [] (e.encode a) ha
      (none, ()) (tapes suffix ((workEncoding e).encode pending) output [] [] [])
    have hin : Function.update (tapes suffix ((workEncoding e).encode pending) output [] [] []) 4 (e.encode a) =
        tapes suffix ((workEncoding e).encode pending) output [] (e.encode a) [] := by
      funext k; fin_cases k <;> rfl
    have hout : Function.update (tapes suffix ((workEncoding e).encode pending) output [] [] []) 4 [] =
        tapes suffix ((workEncoding e).encode pending) output [] [] [] := by
      funext k; fin_cases k <;> rfl
    rw [hin, hout] at hh
    simpa only [labelStmt, List.nil_append, e.decode_encode, Option.elim_some] using congrArg some hh
  convert h.trans (runsExactly_one done) using 1
  omega

theorem fetch_action (a : Action A) (input output : List Bool) (pending : List (Action A))
    (ha : (actionEncode e a).length ≤ C + 8) :
    RunsExactly (machine e C entry).computer.step
      (active e input (a :: pending) output)
      (cfg (actionLabel a) () (tapes input ((workEncoding e).encode pending) output [] [] []))
      (2 * (actionEncode e a).length + 4) := by
  let word := actionEncode e a
  let rest := (workEncoding e).encode pending
  have first : (machine e C entry).computer.step (active e input (a :: pending) output) =
      some (cfg (.fixed 2) () (tapes input (Holant.Algebraic.frame word ++ rest) output [] [] [])) := by
    change some (TM2.stepAux (Machine.Dispatch.fetchStmt (1 : Fin 6) (Label.fixed (A := A) 2) (.fixed 15) (.fixed 18)) (none, ()) _) = _
    simp [Machine.Dispatch.fetchStmt, TM2.stepAux, active, cfg, tapes, workEncoding,
      framedListEncoding, framedListEncode, actionEncoding, word, rest]
    funext k; fin_cases k <;> rfl
  have h := GraphPreprocessing.Frame.extract_exact (1 : Fin 6) 4 5
    (by decide) (by decide) (by decide) (machine e C entry).computer.step (.fixed 2) (.fixed 3) (.fixed 4) (.fixed 18)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) ()
    (tapes input [] output [] [] []) word rest []
  have before : tapes3 (tapes input [] output [] [] []) (1 : Fin 6) 4 5
      (Holant.Algebraic.frame word ++ rest) [] [] = tapes input (Holant.Algebraic.frame word ++ rest) output [] [] [] := by
    funext k; fin_cases k <;> rfl
  have after : tapes3 (tapes input [] output [] [] []) (1 : Fin 6) 4 5 rest (word ++ []) [] =
      tapes input rest output [] word [] := by
    simp only [List.append_nil]
    funext k; fin_cases k <;> rfl
  rw [before, after] at h
  have done : (machine e C entry).computer.step (cfg (.fixed 4) () (tapes input rest output [] word [])) =
      some (cfg (actionLabel a) () (tapes input rest output [] [] [])) := by
    change some (TM2.stepAux (actionStmt e C) (none, ()) _) = _
    have hh := Machine.Dispatch.decodeStmt_exact (4 : Fin 6)
      (fun bits => (actionDecode e bits).elim (.fixed 18) actionLabel) (.fixed 18) (C + 8) [] word ha
      (none, ()) (tapes input rest output [] [] [])
    have hin : Function.update (tapes input rest output [] [] []) 4 word = tapes input rest output [] word [] := by
      funext k; fin_cases k <;> rfl
    have hout : Function.update (tapes input rest output [] [] []) 4 [] = tapes input rest output [] [] [] := by
      funext k; fin_cases k <;> rfl
    rw [hin, hout] at hh
    simpa only [actionStmt, word, List.nil_append, actionDecode_encode, Option.elim_some] using congrArg some hh
  convert ((runsExactly_one first).trans h).trans (runsExactly_one done) using 1
  dsimp only [word]
  omega

end Holant.OneHot.StackProgram.GraphCodeMachine
