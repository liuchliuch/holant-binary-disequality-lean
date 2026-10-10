import Holant.Proofs.CountingMachines.StandardMachine.Support.TapeMicrostepBudget
import Holant.Proofs.CountingMachines.StandardMachine.Support.NDPrimitiveDispatcher.Runs

set_option backward.isDefEq.respectTransparency false
/-! Adapted reference proof. See the task validation reports. Actual unsegmented primitive path equivalence, obtained
by syntax expansion and comparison with internally generated all-raw halting
executions. No path segmentation, simulator, clock or count law is input. The
acceptance protocol is the SAME literal clean true output tape as before. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.NDPrimitiveDispatcher.Paths
open Turing Computability Holant.Complexity
open Program
variable {α Γ : Type} [Fintype Γ] {ea : Encoding α Γ} {f : α → ℕ} (w : SharpPWitness ea f)
abbrev machine := TotalRawSource.source w
def initial (word : List Bool) : Cfg (machine w) := embed (machine w) (PathSegmentation.start w word)
theorem actual_initial (word : List Bool) : initial w word = TM0.init (TapeSimulation.input (machine w) word) := rfl
def clock : Polynomial ℕ := TapeMicrostepBudget.microPolynomial w*Polynomial.C (TapeSimulation.rowBudget (machine w))
theorem clock_eval (word : List Bool) : (clock w).eval word.length =
    (TapeMicrostepBudget.microPolynomial w).eval word.length*TapeSimulation.rowBudget (machine w) := by simp [clock]

abbrev Path (word : List Bool) := {instructions : List (Option Bool) //
  ∃ c : TapeSimulation.FiniteCfg (machine w),
    TapeSimulation.Encoded (machine w) (haltList (machine w).core [true]) (TapeSimulation.forget (machine w) c) ∧
    Runs.Trace (machine w) instructions (initial w word) (embed (machine w) c)}

theorem endpoint_halted (c : TapeSimulation.FiniteCfg (machine w))
    (h : TapeSimulation.Encoded (machine w) (haltList (machine w).core [true]) (TapeSimulation.forget (machine w) c)) :
    Halted (machine w) (embed (machine w) c) :=
  embed_halted (machine w) c (TapeSimulation.accepting_endpoint_halts w c h)

theorem guess_injective (word : List Bool) (p q : Path w word)
    (h : p.val.filterMap id = q.val.filterMap id) : p = q := by
  obtain ⟨c,hc,hr⟩ := p.property
  obtain ⟨d,hd,hs⟩ := q.property
  apply Subtype.ext
  exact (Runs.unique (machine w) p.val q.val _ _ _ hr hs (endpoint_halted w c hc) (endpoint_halted w d hd) h).1

theorem forward_exists (word : List Bool) (p : PathSegmentation.PhysicalPath w word) :
    ∃ q : Path w word, q.val.filterMap id = p.val.filterMap id ∧ q.val.length ≤ (clock w).eval word.length := by
  obtain ⟨c,hc,hr⟩ := p.property
  obtain ⟨instructions,hnative,hlog,hfee⟩ := Runs.expand (machine w) p.val _ c hr
  refine ⟨⟨instructions,c,hc,hnative⟩,hlog,?_⟩
  rw [clock_eval]
  exact hfee.trans (TapeMicrostepBudget.physical_primitive w word p)

/-- Internal all-raw source completion of any observed guess pre. The
extra mathematical choices only select one future trajectory for this proof;
they are not machine input bytes or new branching sites. -/
private theorem complete (word observed : List Bool) :
    ∃ instructions tokens c unused,
      TapeSimulation.InstructionTrace (machine w) tokens (PathSegmentation.start w word) c ∧
      Runs.Trace (machine w) instructions (initial w word) (embed (machine w) c) ∧
      Halted (machine w) (embed (machine w) c) ∧
      observed++List.replicate (TotalRawSource.choiceLength w word) false = instructions.filterMap id++unused ∧
      instructions.filterMap id = tokens.filterMap id ∧ instructions.length ≤ (clock w).eval word.length := by
  let log := observed++List.replicate (TotalRawSource.choiceLength w word) false
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
  obtain ⟨sourceTokens,htime,hlog,hsource⟩ := (machine w).run_trace (TotalRawSource.horizon w word)
    (log,initList (machine w).core word) (unused,TotalRawSource.terminal w word first) hrun
  obtain ⟨c,tokens,hcoded,htape,hguesses,hbudget⟩ := TapeMicrostepBudget.source_path_time w word sourceTokens _ hsource
  obtain ⟨instructions,hnative,hnlog,hfee⟩ := Runs.expand (machine w) tokens _ c htape
  have hc : c.l = none := by
    have hl := TapeSimulation.encoded_label (machine w) _ _ hcoded
    have hh := TotalRawSource.terminal_halts w word first
    cases he : c.l
    · rfl
    · simp [TapeSimulation.forget,hh,he] at hl
  have hcost := (TapeMicrostepBudget.total_source w word tokens c htape).2.1
  refine ⟨instructions,tokens,c,unused,htape,hnative,embed_halted (machine w) c hc,?_,hnlog,?_⟩
  · rw [hnlog,hguesses]
    exact hlog.symm
  · rw [clock_eval]
    exact hfee.trans hcost

/-- Every actual native pre, without a halt/accepted endpoint premise,
is a pre of an internally produced actual native halting transcript. -/
theorem prefix_completion (word : List Bool) (instructions : List (Option Bool)) (finalCfg : Cfg (machine w))
    (h : Runs.Trace (machine w) instructions (initial w word) finalCfg) :
    ∃ rest c, Runs.Trace (machine w) rest finalCfg (embed (machine w) c) ∧
      Halted (machine w) (embed (machine w) c) ∧ (instructions++rest).length ≤ (clock w).eval word.length := by
  obtain ⟨full,tokens,c,unused,htape,hfull,hh,hstream,hlog,hbound⟩ := complete w word (instructions.filterMap id)
  obtain ⟨rest,hcut,hrest⟩ := Runs.prefixTrace (machine w) instructions full _ finalCfg _ h hfull hh
    (List.replicate (TotalRawSource.choiceLength w word) false) unused hstream
  exact ⟨rest,c,hrest,hh,by simpa only [hcut] using hbound⟩

theorem prefix_time (word : List Bool) (instructions : List (Option Bool)) (finalCfg : Cfg (machine w))
    (h : Runs.Trace (machine w) instructions (initial w word) finalCfg) :
    instructions.length ≤ (clock w).eval word.length := by
  obtain ⟨rest,c,hr,hh,hb⟩ := prefix_completion w word instructions finalCfg h
  rw [List.length_append] at hb
  omega

theorem deadline (word : List Bool) (instructions : List (Option Bool)) (finalCfg : Cfg (machine w))
    (h : Runs.Trace (machine w) instructions (initial w word) finalCfg)
    (hlen : instructions.length = (clock w).eval word.length) : Halted (machine w) finalCfg := by
  obtain ⟨rest,c,hr,hh,hb⟩ := prefix_completion w word instructions finalCfg h
  have hz : rest.length = 0 := by rw [List.length_append,hlen] at hb; omega
  have he := List.length_eq_zero_iff.mp hz
  subst rest
  change finalCfg = embed (machine w) c at hr
  exact hr.symm ▸ hh

/-- Reverse consumer for arbitrary unsegmented actual accepting TM0 paths.
Its internally generated completion has the same rows, by genuine halt
uniqueness. The old literal clean-output endpoint is then transported back. -/
theorem reverse_exists (word : List Bool) (p : Path w word) :
    ∃ q : PathSegmentation.PhysicalPath w word, q.val.filterMap id = p.val.filterMap id := by
  obtain ⟨accept,haccept,hpath⟩ := p.property
  obtain ⟨full,tokens,c,unused,htape,hfull,hh,hstream,hlog,hbound⟩ := complete w word (p.val.filterMap id)
  obtain ⟨rest,hcut,hrest⟩ := Runs.prefixTrace (machine w) p.val full _ _ _ hpath hfull hh
    (List.replicate (TotalRawSource.choiceLength w word) false) unused hstream
  obtain ⟨hz,hend⟩ := Runs.halted_trace (machine w) rest _ _ (endpoint_halted w accept haccept) hrest
  have hwords : full = p.val := by simpa only [hz,List.append_nil] using hcut
  have hcfg : accept = c := embed_injective (machine w) hend
  have hc := hcfg ▸ haccept
  refine ⟨⟨tokens,c,hc,htape⟩,?_⟩
  exact hlog.symm.trans (congrArg (List.filterMap id) hwords)

def forward (word : List Bool) (p : PathSegmentation.PhysicalPath w word) : Path w word :=
  Classical.choose (forward_exists w word p)
def backward (word : List Bool) (p : Path w word) : PathSegmentation.PhysicalPath w word :=
  Classical.choose (reverse_exists w word p)
theorem forward_log (word : List Bool) (p : PathSegmentation.PhysicalPath w word) :
    (forward w word p).val.filterMap id = p.val.filterMap id := (Classical.choose_spec (forward_exists w word p)).1
theorem backward_log (word : List Bool) (p : Path w word) :
    (backward w word p).val.filterMap id = p.val.filterMap id := Classical.choose_spec (reverse_exists w word p)

def pathsEquiv (word : List Bool) : PathSegmentation.PhysicalPath w word ≃ Path w word where
  toFun := forward w word
  invFun := backward w word
  left_inv p := PathSegmentation.physical_guess_injective w word _ p
    ((backward_log w word (forward w word p)).trans (forward_log w word p))
  right_inv p := guess_injective w word _ p
    ((forward_log w word (backward w word p)).trans (backward_log w word p))

noncomputable instance (word : List Bool) : Fintype (Path w word) :=
  Fintype.ofEquiv (PathSegmentation.PhysicalPath w word) (pathsEquiv w word)
def count (word : List Bool) : ℕ := Fintype.card (Path w word)
theorem raw_count (word : List Bool) : count w word = PathSegmentation.count w word :=
  Fintype.card_congr (pathsEquiv w word).symm
def originalPathsEquiv (a : α) : ConventionalSharpPSource.AcceptedWitness w a ≃
    Path w (TotalRawSource.encodedInput w a) := (PathSegmentation.originalPathsEquiv w a).trans (pathsEquiv w _)
theorem encoded_count (a : α) : count w (TotalRawSource.encodedInput w a) = f a :=
  (raw_count w _).trans (PathSegmentation.encoded_count w a)

end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.NDPrimitiveDispatcher.Paths
