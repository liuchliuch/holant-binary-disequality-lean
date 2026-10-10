import Holant.Complexity.UniversalPairReduction.SmoothingCompiler.ThreeQueryProgram
import Holant.Complexity.UniversalPairReduction.SmoothingCompiler.ThreeQueryCount
import Holant.Complexity.UniversalPairReduction.SmoothingCompiler.ControlLabels

/-! The concrete collector performs at most three queries on every actual run
prefix, including malformed inputs and arbitrary oracle extensions. -/
namespace Holant.Complexity.UniversalPairReduction.ThreeQuery
open Turing BinaryCompose SmoothingCompiler
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option Elab.async false
variable (a b : BinaryCompose.Machine)

def remainingLabel : Option (Labels a b) → ℕ
  | none => 0
  | some (.inl _) => 3
  | some (.inr (.inl _)) => 0
  | some (.inr (.inr i)) => if i.val ≤ 2 then 3 else if i.val ≤ 6 then 2 else if i.val ≤ 10 then 1 else 0

def remaining (c : (machine a b).Cfg) : ℕ := remainingLabel a b c.l

theorem remaining_le_three (c : (machine a b).Cfg) : remaining a b c ≤ 3 := by
  rcases c with ⟨l,state,tapes⟩
  cases l with
  | none => exact Nat.zero_le 3
  | some l =>
    cases l with
    | inl l => exact Nat.le_refl 3
    | inr l =>
      cases l with
      | inl l => exact Nat.zero_le 3
      | inr i => simp only [remaining,remainingLabel]; split_ifs <;> omega

theorem potential (oracle : List Bool → List Bool) (c d : (machine a b).Cfg)
    (h : (machine a b).step oracle c = some d) :
    queryCost (machine a b) c + remaining a b d ≤ remaining a b c := by
  rcases c with ⟨l,state,tapes⟩
  cases l with
  | none => simp [OracleMachine.step] at h
  | some l =>
    cases l with
    | inl l =>
      change 0 + remaining a b d ≤ 3
      simpa only [Nat.zero_add] using remaining_le_three a b d
    | inr l =>
      cases l with
      | inl l =>
        change some (TM2.stepAux (embedStmt (rightLayout a b) (rightStates a b)
          (secondLabel a b) none (b.program l)) state tapes) = some d at h
        have hd := Option.some.inj h
        subst d
        change 0 + remaining a b _ ≤ 0
        rcases embedStmt_label_cases (rightLayout a b) (rightStates a b)
          (secondLabel a b) none (b.program l) state tapes with hl | ⟨j,hl⟩
        · simp [remaining,hl,remainingLabel]
        · simp [remaining,hl,remainingLabel,secondLabel]
      | inr i =>
        fin_cases i
        all_goals try { change 0 + remaining a b d ≤ 3; simpa only [Nat.zero_add] using remaining_le_three a b d }
        all_goals simp only [OracleMachine.step,machine,program,protocol] at h
        all_goals try simp only [Fin.isValue,Fin.reduceEq,ite_true,ite_false] at h
        all_goals have hd := Option.some.inj h
        all_goals subst d
        all_goals simp [queryCost,machine,program,protocol,remaining,remainingLabel,admin,
          GraphPreprocessing.Frame.scanStmt,StackProtocol.copyMoveStmt,
          FixedFieldMachines.FrameEmit.delimiterStmt,FixedFieldMachines.FrameEmit.emitStmt,
          TM2.stepAux,secondLabel]
        all_goals split_ifs <;> (first | rfl | exact Nat.zero_le _)

/-- A numerical bound on actual oracle transitions, not merely query labels. -/
theorem atMostThree : AtMostQueries (machine a b) 3 := by
  intro oracle input n
  have h := queryCount_le_of_potential (machine a b) oracle (remaining a b)
    (potential a b oracle) ((machine a b).init input) n
  exact le_trans h (remaining_le_three a b _)

end Holant.Complexity.UniversalPairReduction.ThreeQuery
