import Holant.Complexity.FixedFieldMachines.FrameEmit
import Holant.Complexity.OracleMachine

/-! Actual framed query parsing and answer serialization while preserving a
caller context. Only the decoded query tape is exposed to the oracle. -/
namespace Holant.Complexity.OracleOneQuery.FramedQuery
open Turing StackProtocol Holant.Algebraic FixedFieldMachines

variable {K Λ τ : Type} [DecidableEq K]

private theorem swap_tapes (src dst tmp : K) (hsd : src ≠ dst)
    (frame : K → List Bool) (a b c : List Bool) :
    tapes3 frame src dst tmp a b c = tapes3 frame dst src tmp b a c := by
  unfold tapes3
  rw [Function.update_comm hsd]

/-- The query transition has the literal oracle semantics on its designated tape. -/
def QueriesAt (step : Cfg K Λ τ → Option (Cfg K Λ τ)) (query next : Λ)
    (key : K) (oracle : List Bool → List Bool) : Prop :=
  ∀ state tapes, step ⟨some query, state, tapes⟩ =
    some ⟨some next, state, Function.update tapes key (oracle (tapes key))⟩

/-- Parse the first framed word, query only that word, and reconstruct an encoded
pair with the untouched suffix. All query and temporary tapes are cleared. -/
theorem exact_run (src queryKey tmp : K)
    (hsq : src ≠ queryKey) (hst : src ≠ tmp) (hqt : queryKey ≠ tmp)
    (step : Cfg K Λ τ → Option (Cfg K Λ τ))
    (scan restore query move delimiter emit next bad : Λ)
    (hs : ExecutesAt step scan (GraphPreprocessing.Frame.scanStmt src tmp scan restore bad))
    (hr : ExecutesAt step restore (copyMoveStmt tmp queryKey restore query))
    (oracle : List Bool → List Bool) (hq : QueriesAt step query move queryKey oracle)
    (hm : ExecutesAt step move (copyMoveStmt queryKey tmp move delimiter))
    (hd : ExecutesAt step delimiter (FrameEmit.delimiterStmt src emit))
    (he : ExecutesAt step emit (FrameEmit.emitStmt tmp src emit next))
    (memory : τ) (tapes : K → List Bool) (word context : List Bool) :
    RunsExactly step
      (cfg scan memory (tapes3 tapes src queryKey tmp (frame word ++ context) [] []))
      (cfg next memory (tapes3 tapes src queryKey tmp (frame (oracle word) ++ context) [] []))
      (2 * word.length + 2 * (oracle word).length + 6) := by
  have parse := GraphPreprocessing.Frame.extract_exact src queryKey tmp hsq hst hqt
    step scan restore query bad hs hr memory tapes word context []
  simp only [List.append_nil] at parse
  have call : RunsExactly step
      (cfg query memory (tapes3 tapes src queryKey tmp context word []))
      (cfg move memory (tapes3 tapes src queryKey tmp context (oracle word) [])) 1 := by
    apply runsExactly_one
    rw [cfg, hq]
    simp only [tapes3_dst src queryKey tmp hqt,
      update_tapes3_dst src queryKey tmp hqt, cfg]
  have emitRun := FrameEmit.prepend_exact queryKey src tmp (Ne.symm hsq) hqt hst
    step move delimiter emit next hm hd he memory tapes (oracle word) context
  rw [← swap_tapes src queryKey tmp hsq, ← swap_tapes src queryKey tmp hsq] at emitRun
  have h := (parse.trans call).trans emitRun
  convert h using 1 <;> omega

end Holant.Complexity.OracleOneQuery.FramedQuery
