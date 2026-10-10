import Holant.Proofs.CountingMachines.StandardMachine.Support.NDPrimitiveFrontend.Composition
import Holant.Proofs.CountingMachines.StandardMachine.Support.NDPrimitiveAcceptControl.Program

set_option backward.isDefEq.respectTransparency false
/-! Adapted reference proof. See the task validation reports. Actual halt-output receipts. Density of each original
stack is proved by the existing TrCfg projection, so an observed blank in the
next full column is strict EOF for every stack. This is not a runtime decoder. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.NDPrimitiveAcceptControl.Observation
open Turing Computability Holant.Complexity
open Program
variable {α Γ : Type} [Fintype Γ] {ea : Encoding α Γ} {f : α → ℕ} (w : SharpPWitness ea f)

theorem head_stack (d : (machine w).Config) (c : TapeSimulation.FiniteCfg (machine w))
    (h : TapeSimulation.Encoded (machine w) d (TapeSimulation.forget (machine w) c)) (k : (machine w).core.K) :
    (d.stk k).reverse[0]? = c.Tape.head.2 k := by
  simpa only [TapeSimulation.forget,Tape.right₀,ListBlank.nth_zero,ListBlank.head_cons] using
    TapeSimulation.encoded_stack (machine w) d _ h k 0
theorem next_stack (d : (machine w).Config) (c : TapeSimulation.FiniteCfg (machine w))
    (h : TapeSimulation.Encoded (machine w) d (TapeSimulation.forget (machine w) c)) (k : (machine w).core.K) :
    (d.stk k).reverse[1]? = c.Tape.right.head.2 k := by
  simpa only [TapeSimulation.forget,Tape.right₀,ListBlank.nth_succ,ListBlank.tail_cons,ListBlank.nth_zero] using
    TapeSimulation.encoded_stack (machine w) d _ h k 1
theorem bottom_flag (d : (machine w).Config) (c : TapeSimulation.FiniteCfg (machine w))
    (h : TapeSimulation.Encoded (machine w) d (TapeSimulation.forget (machine w) c)) : c.Tape.head.1 = true := by
  have hb (a : TapeSimulation.Cfg (machine w)) (ha : TapeSimulation.Encoded (machine w) d a) : a.Tape.head.1 = true := by
    cases ha
    exact TM2to1.addBottom_head_fst _
  exact hb _ h
theorem next_flag (d : (machine w).Config) (c : TapeSimulation.FiniteCfg (machine w))
    (h : TapeSimulation.Encoded (machine w) d (TapeSimulation.forget (machine w) c)) : c.Tape.right.head.1 = false := by
  have hb (a : TapeSimulation.Cfg (machine w)) (ha : TapeSimulation.Encoded (machine w) d a) : a.Tape.right.head.1 = false := by
    cases ha
    simpa only [Tape.mk'_right,ListBlank.nth_succ,ListBlank.nth_zero] using TM2to1.addBottom_nth_succ_fst _ 0
  exact hb _ h
theorem label_none (d : (machine w).Config) (c : TapeSimulation.FiniteCfg (machine w))
    (h : TapeSimulation.Encoded (machine w) d (TapeSimulation.forget (machine w) c)) (hd : d.l = none) : c.l = none := by
  have hl := TapeSimulation.encoded_label (machine w) d _ h
  cases hc : c.l <;> simp [hd,TapeSimulation.forget,hc] at hl ⊢

theorem true_columns (c : TapeSimulation.FiniteCfg (machine w))
    (h : TapeSimulation.Encoded (machine w) (haltList (machine w).core [true]) (TapeSimulation.forget (machine w) c)) :
    c.l = none ∧ c.var = (machine w).core.initialState ∧
      c.Tape.head = trueColumn w ∧ c.Tape.right.head = default := by
  have hl := label_none w _ c h rfl
  have hv := (TapeSimulation.encoded_state (machine w) _ _ h).symm
  have hh : c.Tape.head = trueColumn w := by
    apply Prod.ext
    · exact bottom_flag w _ c h
    · funext k
      have hs := head_stack w _ c h k
      by_cases hk : k = (machine w).core.k₁
      · subst k; simpa [haltList,trueColumn] using hs.symm
      · simpa [haltList,trueColumn,hk] using hs.symm
  have ht : c.Tape.right.head = default := by
    apply Prod.ext
    · exact next_flag w _ c h
    · funext k
      have hs := next_stack w _ c h k
      change c.Tape.right.head.2 k = none
      by_cases hk : k = (machine w).core.k₁
      · subst k; simpa [haltList] using hs.symm
      · simpa [haltList,hk] using hs.symm
  exact ⟨hl,hv,hh,ht⟩

theorem observed_true_iff (d : (machine w).Config) (c : TapeSimulation.FiniteCfg (machine w))
    (he : TapeSimulation.Encoded (machine w) d (TapeSimulation.forget (machine w) c)) (hd : d.l = none) :
    (headGood w (Old.lift w (Native.embed (machine w) c)).q
      (Old.lift w (Native.embed (machine w) c)).Tape.head = true ∧
      (Old.lift w (Native.embed (machine w) c)).Tape.right.head = default) ↔
      TapeSimulation.Encoded (machine w) (haltList (machine w).core [true]) (TapeSimulation.forget (machine w) c) := by
  have hl := label_none w d c he hd
  constructor
  · rintro ⟨hgood,hblank⟩
    have hfields : c.var = (machine w).core.initialState ∧ c.Tape.head = trueColumn w := by
      simpa [headGood,Old.lift,Old.inclusion,Native.embed,Native.haltCfg,hl,Tape.map_fst] using hgood
    have ht : c.Tape.right.head = default := by
      simpa [Old.lift,Old.inclusion,Native.embed,Native.haltCfg,hl,Tape.map,ListBlank.head_map] using hblank
    have hv : d.var = (machine w).core.initialState := (TapeSimulation.encoded_state (machine w) d _ he).trans hfields.1
    have hS : d.stk = (haltList (machine w).core [true]).stk := by
      funext k
      have h0 := head_stack w d c he k
      have h1 := next_stack w d c he k
      have hz : (d.stk k).reverse[1]? = none := by rw [ht] at h1; exact h1
      have hlen : (d.stk k).reverse.length ≤ 1 := List.getElem?_eq_none_iff.mp hz
      apply List.reverse_injective
      apply List.ext_getElem?
      intro n
      cases n with
      | zero =>
          rw [h0,hfields.2]
          by_cases hk : k = (machine w).core.k₁
          · subst k; simp [haltList,trueColumn]
          · simp [haltList,trueColumn,hk]
      | succ n =>
          rw [List.getElem?_eq_none (by omega)]
          by_cases hk : k = (machine w).core.k₁
          · subst k; simp [haltList]
          · simp [haltList,hk]
    have hfinal : d = haltList (machine w).core [true] := by
      cases d; cases hd; cases hv; cases hS; rfl
    exact hfinal ▸ he
  · intro ht
    obtain ⟨hl,hv,hh,hnext⟩ := true_columns w c ht
    simp [headGood,Old.lift,Old.inclusion,Native.embed,Native.haltCfg,hl,Tape.map,ListBlank.head_map,hv,hh,hnext]

/-- The original all-raw, all-choice execution produces the encoded unknown
Boolean terminal. Comparing actual primitive traces recovers this receipt at
any observed real halt; no accepted verdict is selected by the caller. -/
theorem native_halt_encoding (word : List Bool) (tokens : List (Option Bool)) (finalCfg : Native.Cfg (machine w))
    (hr : NDPrimitiveDispatcher.Runs.Trace (machine w) tokens (NDPrimitiveDispatcher.Paths.initial w word) finalCfg)
    (hh : Native.Halted (machine w) finalCfg) :
    ∃ choices c, finalCfg = Native.embed (machine w) c ∧
      TapeSimulation.Encoded (machine w) (TotalRawSource.terminal w word choices) (TapeSimulation.forget (machine w) c) := by
  let log := tokens.filterMap id++List.replicate (TotalRawSource.choiceLength w word) false
  let first := log.take (TotalRawSource.choiceLength w word)
  let unused := log.drop (TotalRawSource.choiceLength w word)
  have hge : TotalRawSource.choiceLength w word ≤ log.length := by
    simp only [log,List.length_append,List.length_replicate]
    omega
  have hlen : first.length = TotalRawSource.choiceLength w word := by simp [first,Nat.min_eq_left hge]
  have hsplit : first++unused = log := List.take_append_drop _ _
  have hrun : (machine w).run (TotalRawSource.horizon w word) (log,initList (machine w).core word) =
      some (unused,TotalRawSource.terminal w word first) := by
    simpa only [hsplit] using TotalRawSource.all_raw_run w word first unused hlen
  obtain ⟨sourceTokens,htime,hlog,hsource⟩ := (machine w).run_trace (TotalRawSource.horizon w word) _ _ hrun
  obtain ⟨c,tapeTokens,hencoded,htape,hguesses,hbudget⟩ := TapeMicrostepBudget.source_path_time w word sourceTokens _ hsource
  obtain ⟨full,hfull,hfullLog,hfee⟩ := NDPrimitiveDispatcher.Runs.expand (machine w) tapeTokens _ c htape
  have hl := label_none w _ c hencoded (TotalRawSource.terminal_halts w word first)
  have hhalt : Native.Halted (machine w) (Native.embed (machine w) c) :=
    NDPrimitiveDispatcher.Program.embed_halted (machine w) c hl
  have hstream : tokens.filterMap id++List.replicate (TotalRawSource.choiceLength w word) false = full.filterMap id++unused := by
    rw [hfullLog,hguesses]
    exact hlog.symm
  obtain ⟨rest,hcut,hrest⟩ := NDPrimitiveDispatcher.Runs.prefixTrace (machine w) tokens full _ finalCfg _ hr hfull hhalt
    (List.replicate (TotalRawSource.choiceLength w word) false) unused hstream
  have hend := (NDPrimitiveDispatcher.Runs.halted_trace (machine w) rest _ _ hh hrest).2
  exact ⟨first,c,hend,hencoded⟩

theorem actual_halt_encoding (word : List Bool) (tokens : List (Option Bool)) (finalCfg : Old.Cfg w)
    (hr : NDPrimitiveFrontend.Composition.Trace w tokens (Old.initial w word) finalCfg)
    (hh : terminal w finalCfg.q = true) :
    ∃ choices c, finalCfg = Old.lift w (Native.embed (machine w) c) ∧
      TapeSimulation.Encoded (machine w) (TotalRawSource.terminal w word choices) (TapeSimulation.forget (machine w) c) := by
  obtain ⟨suffix,hcut,htrace⟩ := NDPrimitiveFrontend.Composition.split_prepare w word tokens finalCfg hr
    (terminal_right w finalCfg.q hh)
  obtain ⟨native,hnative,heq⟩ := NDPrimitiveFrontend.Composition.reflect_trace w suffix _ finalCfg htrace
  have hn : Native.Halted (machine w) native := (terminal_native w native).mp (heq.symm ▸ hh)
  obtain ⟨choices,c,hc,hencoded⟩ := native_halt_encoding w word suffix native hnative hn
  exact ⟨choices,c,heq.symm.trans (congrArg (Old.lift w) hc),hencoded⟩

end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.NDPrimitiveAcceptControl.Observation
