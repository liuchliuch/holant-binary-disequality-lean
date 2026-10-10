import Holant.OneHot.StackProgram.GraphCodeMachine.Components.Stages

namespace Holant.OneHot.StackProgram.GraphCodeMachine.Components
open Turing Computability Holant.Complexity BinaryCompose StackProtocol
variable (m : BinaryCompose.Machine) (z o a p : List Bool)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 512
set_option maxHeartbeats 800000

/-- Fetch and physically unframe exactly one component, preserving every suffix. -/
theorem fetch_exact (word suffix output count : List Bool) :
    RunsExactly (machine m z o a p).computer.step
      (active m 0 (true :: Holant.Algebraic.frame word ++ suffix) [] output count)
      (active m 3 suffix word output count) (2 * word.length + 3) := by
  have first : (machine m z o a p).computer.step
      (active m 0 (true :: Holant.Algebraic.frame word ++ suffix) [] output count) =
      some (active m 1 (Holant.Algebraic.frame word ++ suffix) [] output count) := by
    change some (cfg (Sum.inr 1 : Labels m) m.initial
      (Function.update (base m (true :: Holant.Algebraic.frame word ++ suffix) [] output count)
        (.inr 0) (Holant.Algebraic.frame word ++ suffix))) = _
    congr 2; funext key; cases key with
    | inl k => rfl
    | inr k => fin_cases k <;> rfl
  have h := GraphPreprocessing.Frame.extract_exact (.inr 0 : Keys m) (.inr 1) (.inr 2)
    (by simp) (by simp) (by simp) (machine m z o a p).computer.step
    (.inr 1) (.inr 2) (.inr 3) (.inr 25)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl)
    m.initial (base m suffix [] output count) word suffix []
  have hs : tapes3 (base m suffix [] output count) (.inr 0) (.inr 1) (.inr 2)
      (Holant.Algebraic.frame word ++ suffix) [] [] = base m (Holant.Algebraic.frame word ++ suffix) [] output count := by
    funext key; cases key with
    | inl k => rfl
    | inr k => fin_cases k <;> rfl
  have ht : tapes3 (base m suffix [] output count) (.inr 0) (.inr 1) (.inr 2)
      suffix (word ++ []) [] = base m suffix word output count := by
    simp only [List.append_nil]
    funext key; cases key with
    | inl k => rfl
    | inr k => fin_cases k <;> rfl
  rw [hs, ht] at h
  convert (runsExactly_one first).trans h using 1
  rfl

theorem tag_exact (b c : Bool) (input rest output count : List Bool) :
    (machine m z o a p).computer.step (active m 3 input (b :: c :: rest) output count) =
      some (active m (if b then if c then 25 else 8 else if c then 4 else 17) input rest output count) := by
  cases b <;> cases c
  all_goals change some (TM2.stepAux (tagStmt m) (none, m.initial) _) = _
  all_goals dsimp [tagStmt, takeBit, jump, TM2.stepAux, active, cfg, base, tapes]
  all_goals simp only [Bool.cond_false, Bool.cond_true, Function.update_self,
    List.head?_cons, List.tail_cons, Option.isSome_some, Option.getD_some, Function.update_idem]
  all_goals congr 2; funext key; cases key with
    | inl k => rfl
    | inr k => fin_cases k <;> rfl

theorem push_exact (phase next : Fin 26) (word : List Bool)
    (hp : (machine m z o a p).program (.inr phase) =
      FixedFieldMachines.Constant.pushWord (.inr 3) word (TM2.Stmt.goto (fun _ => .inr next)))
    (input descriptor output count : List Bool) :
    (machine m z o a p).computer.step (active m phase input descriptor output count) =
      some (active m next input descriptor (word ++ output) count) := by
  change some (TM2.stepAux ((machine m z o a p).program (.inr phase)) (none, m.initial) _) = _
  rw [hp, FixedFieldMachines.Constant.pushWord_eval]
  change some (cfg (Sum.inr next : Labels m) m.initial
    (Function.update (base m input descriptor output count) (.inr 3) (word ++ output))) = _
  congr 2; funext key; cases key with
  | inl k => rfl
  | inr k => fin_cases k <;> rfl

theorem finish_descriptor (input output count : List Bool) :
    (machine m z o a p).computer.step (active m 20 input [] output count) =
      some (active m 0 input [] output (true :: count)) := by
  change some (TM2.stepAux (finishDescriptor m) (none, m.initial) (base m input [] output count)) = _
  dsimp [finishDescriptor, jump, TM2.stepAux, active, cfg, base, tapes]
  simp only [Bool.cond_false, Function.update_of_ne (show (Sum.inr (5 : Fin 6) : Keys m) ≠ .inr 1 by simp)]
  congr 2; funext key; cases key with
  | inl k => simp [Function.update]
  | inr k => fin_cases k <;> simp [Function.update]

/-- One actual pop of each unary component count emits one fixed multiplication chunk. -/
theorem count_exact (n : ℕ) (output : List Bool) :
    RunsExactly (machine m z o a p).computer.step
      (active m 21 [] [] output (List.replicate n true))
      (active m 22 [] [] ((List.replicate n p).flatten ++ output) []) (n + 1) := by
  induction n generalizing output with
  | zero =>
    apply runsExactly_one
    change some (TM2.stepAux (countStmt m p) (none, m.initial) (base m [] [] output [])) = _
    dsimp [countStmt, takeBit, jump, TM2.stepAux, active, cfg, base, tapes]
    simp only [Bool.cond_false]
    congr 2; funext key; cases key with
    | inl k => simp [Function.update]
    | inr k => fin_cases k <;> simp [Function.update]
  | succ n ih =>
    have first : (machine m z o a p).computer.step
        (active m 21 [] [] output (List.replicate (n + 1) true)) =
        some (active m 21 [] [] (p ++ output) (List.replicate n true)) := by
      change some (TM2.stepAux (countStmt m p) (none, m.initial)
        (base m [] [] output (true :: List.replicate n true))) = _
      dsimp [countStmt, takeBit, TM2.stepAux, base, tapes]
      simp only [Bool.cond_true]
      rw [FixedFieldMachines.Constant.pushWord_eval]
      dsimp [jump, TM2.stepAux, active, cfg, base, tapes]
      simp only [Function.update_of_ne (show (Sum.inr (3 : Fin 6) : Keys m) ≠ .inr 5 by simp)]
      congr 2; funext key; cases key with
      | inl k => simp [Function.update]
      | inr k => fin_cases k <;> simp [Function.update]
    have all := (runsExactly_one first).trans (ih (p ++ output))
    have hr : (List.replicate n p).flatten ++ p = (List.replicate (n + 1) p).flatten := by
      rw [List.replicate_succ', List.flatten_append]
      simp
    simpa only [← List.append_assoc, hr, Nat.add_assoc] using all

end Holant.OneHot.StackProgram.GraphCodeMachine.Components
