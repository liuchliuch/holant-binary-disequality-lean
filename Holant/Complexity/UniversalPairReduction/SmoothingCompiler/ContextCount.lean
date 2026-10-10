import Holant.Complexity.UniversalPairReduction.SmoothingCompiler.ThreeQueryCount
import Holant.Complexity.OracleOneQuery.ContextProgram
import Holant.Complexity.UniversalPairReduction.SmoothingCompiler.ControlLabels

/-! A query bound on every actual prefix of the existing one-query context
caller, independently of the oracle, input bytes, or termination. -/
namespace Holant.Complexity.UniversalPairReduction.SmoothingCompiler
open Turing BinaryCompose
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option Elab.async false


namespace ContextCount
open OracleOneQuery.Context ThreeQuery
variable (a b : BinaryCompose.Machine)

def remainingLabel : Option (Labels a b) → ℕ
  | none => 0
  | some (.inl _) => 1
  | some (.inr (.inl _)) => 0
  | some (.inr (.inr i)) => if i.val≤2 then 1 else 0

def remaining (c : (machine a b).Cfg) : ℕ := remainingLabel a b c.l

theorem remaining_le_one (c : (machine a b).Cfg) : remaining a b c ≤ 1 := by
  rcases c with ⟨l,state,tapes⟩
  cases l with
  | none => exact Nat.zero_le 1
  | some l =>
    cases l with
    | inl l => exact Nat.le_refl 1
    | inr l =>
      cases l with
      | inl l => exact Nat.zero_le 1
      | inr i => simp [remaining,remainingLabel]; split <;> omega

theorem potential (oracle : List Bool → List Bool) (c d : (machine a b).Cfg)
    (h : (machine a b).step oracle c=some d) :
    queryCost (machine a b) c + remaining a b d ≤ remaining a b c := by
  rcases c with ⟨l,state,tapes⟩
  cases l with
  | none => simp [OracleMachine.step] at h
  | some l =>
    cases l with
    | inl l =>
      change 0 + remaining a b d ≤ 1
      simpa only [Nat.zero_add] using remaining_le_one a b d
    | inr l =>
      cases l with
      | inl l =>
        change some (TM2.stepAux (embedStmt (a.rightLayout b) (a.rightStates b)
          (secondLabel a b) none (b.program l)) state tapes)=some d at h
        have hd := Option.some.inj h
        subst d
        change 0 + remaining a b _ ≤ 0
        rcases embedStmt_label_cases (a.rightLayout b) (a.rightStates b)
          (secondLabel a b) none (b.program l) state tapes with hl|⟨j,hl⟩
        · simp [remaining,hl,remainingLabel]
        · simp [remaining,hl,remainingLabel,secondLabel]
      | inr i =>
        fin_cases i
        all_goals try { change 0 + remaining a b d ≤ 1; simpa only [Nat.zero_add] using remaining_le_one a b d }
        all_goals simp only [OracleMachine.step,machine,program] at h
        all_goals try simp only [Fin.isValue,Fin.reduceEq,ite_true,ite_false] at h
        all_goals have hd := Option.some.inj h
        all_goals subst d
        all_goals simp [queryCost,machine,program,remaining,remainingLabel,admin,
          StackProtocol.copyMoveStmt,FixedFieldMachines.FrameEmit.delimiterStmt,
          FixedFieldMachines.FrameEmit.emitStmt,TM2.stepAux,secondLabel]
        all_goals split_ifs <;> rfl

theorem atMostOne : AtMostQueries (machine a b) 1 := by
  intro oracle input n
  have h := queryCount_le_of_potential (machine a b) oracle (remaining a b)
    (potential a b oracle) ((machine a b).init input) n
  exact le_trans h (remaining_le_one a b _)

end ContextCount
end Holant.Complexity.UniversalPairReduction.SmoothingCompiler
