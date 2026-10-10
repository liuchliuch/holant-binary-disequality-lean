import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.CountsPackage

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.CountsPackage
open Turing Computability StackProtocol BinaryCompose
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option Elab.async false

theorem embedded_initial (input : List Bool) :
    Returning.cfg (initList NetworkCounts.machine.computer input) (Fin.elim0 : Fin 0 → List Bool) =
      initList machine.computer input := by
  rw [Machine.init_eq,Machine.init_eq]
  dsimp only [Returning.cfg,Option.map_some]
  congr 1
  funext k
  cases k with
  | inl k => fin_cases k <;> rfl
  | inr k => exact Fin.elim0 k

/-- Actual copies, outer-frame parsing and both list counters, including return. -/
theorem read_counts (r : RawClosedNetwork) :
    RunsExactly (TM2.step program) (initList machine.computer (RawClosedNetwork.encoding.encode r))
      (config (.inr 0) (RawClosedNetwork.encoding.encode r)
        (List.replicate r.vertices.length true) (List.replicate r.edges.length true) [])
      (NetworkCounts.transitionCount r+1) := by
  have h := Returning.run_active NetworkCounts.machine.program returns controller _ _
    (Fin.elim0 : Fin 0 → List Bool) _ (NetworkCounts.prepare_exact r) rfl
  have ret := Returning.return_step NetworkCounts.machine.program returns controller (8 : Fin 10) rfl
    (none,()) (NetworkCounts.result r).stk (Fin.elim0 : Fin 0 → List Bool)
  change RunsExactly (TM2.step program) _ _ _ at h
  change TM2.step program _ = _ at ret
  rw [embedded_initial] at h
  simpa [Returning.cfg,NetworkCounts.result,config,work,returns,cfg,Nat.add_comm] using h.trans (runsExactly_one ret)

theorem work_empty : work [] [] [] [] = fun _ => [] := by
  funext k
  cases k with
  | inl k => fin_cases k <;> rfl
  | inr k => exact Fin.elim0 k

theorem halt_step (output : List Bool) :
    TM2.step program (config (.inr 6) [] [] output []) = some (haltList machine.computer output) := by
  rw [Machine.halt_eq]
  have h := update_output [] [] [] [] output
  rw [work_empty] at h
  change wordTape (Sum.inl 6 : Stack) output = _ at h
  change some (⟨none,(none,()),work [] [] output []⟩ : TM2.Cfg (fun _ : Stack => Bool) Label (Option Bool × Unit)) = _
  rw [← h]

def ticks (r : RawClosedNetwork) : ℕ :=
  NetworkCounts.transitionCount r+2*r.vertices.length+2*(RawClosedNetwork.encoding.encode r).length+8

/-- All counters are physically derived from the raw serialized records. -/
theorem exact_run (r : RawClosedNetwork) :
    RunsExactly machine.computer.step (initList machine.computer (RawClosedNetwork.encoding.encode r))
      (haltList machine.computer (word r)) (ticks r) := by
  have all := (((read_counts r).trans (frame_vertices (RawClosedNetwork.encoding.encode r)
    (List.replicate r.vertices.length true) (List.replicate r.edges.length true))).trans
    (frame_raw (RawClosedNetwork.encoding.encode r)
      (Holant.Algebraic.frame (List.replicate r.vertices.length true) ++ List.replicate r.edges.length true))).trans
    (runsExactly_one (halt_step (word r)))
  have ht : ticks r = 1+(2*(RawClosedNetwork.encoding.encode r).length+3+
      (2*(List.replicate r.vertices.length true).length+3+(NetworkCounts.transitionCount r+1))) := by
    simp only [ticks,List.length_replicate]
    omega
  rw [ht]
  exact all

theorem ticks_le (r : RawClosedNetwork) : ticks r ≤ 8*(RawClosedNetwork.encoding.encode r).length+12 := by
  have hc := NetworkCounts.transitionCount_le r
  have hn := r.counts_le_encoded_length
  unfold ticks
  omega

theorem word_length (r : RawClosedNetwork) : (word r).length ≤ 4*(RawClosedNetwork.encoding.encode r).length+2 := by
  have hn := r.counts_le_encoded_length
  simp only [word,List.length_append,Holant.Algebraic.frame_length,List.length_replicate]
  omega

noncomputable def computes : Computes RawClosedNetwork.encoding Frame.wordEncoding word where
  machine := machine
  time := 8*Polynomial.X+12
  outputs r := {steps := ticks r, evals_in_steps := exact_run r, steps_le_m := by simpa using ticks_le r}

theorem inFP : InFP RawClosedNetwork.encoding Frame.wordEncoding word := computes.inFP

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.CountsPackage
