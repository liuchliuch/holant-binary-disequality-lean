import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualCoefficientControl

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualCoefficientInput
open Turing Computability StackProtocol BinaryCompose
open Holant.OneHot.StackProgram.GraphLabelEncoding
variable (s b : ℕ) (arity : ℕ → ℕ)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 400000
set_option Elab.async false

/-- Call the real original-signature/residual-descriptor emitter and charge its return. -/
theorem call_coefficient (x : Input s b arity) :
    let raw := RawClosedNetwork.encoding.encode x.1.1.val
    let vertex := List.replicate x.1.2.1.val true
    let descriptor := ResidualVertex.descriptorWord x.1.1.val x.1.2.1 x.2
    let word := (treeLabelEncoding s b arity).encode (literal s b arity x)
    RunsExactly (TM2.step (program s b arity))
      (config s arity (.inl (ResidualVertex.sourceLabel s arity (.inr 0))) [] [] raw vertex descriptor [] [])
      (config s arity (.inr 9) [] [] raw vertex descriptor word [])
      (ResidualVertex.ticks false x.1.1.val x.1.1.property x.1.2.1 x.2 + 1) := by
  have source := ResidualVertex.exact_run false x.1.1.val x.1.1.property x.1.2.1 x.2 []
  simp only [ResidualVertex.outputWord,Bool.false_eq_true,↓reduceIte,List.append_nil] at source
  have run := Returning.run_active (ResidualVertex.program s b arity false) (returns s arity) (controller s arity)
    _ _ ![[],[],[]] _ source rfl
  have ret := Returning.return_step (ResidualVertex.program s b arity false) (returns s arity) (controller s arity)
    (ResidualVertex.phase s arity 7) rfl (none,())
    (ResidualVertex.work (RawClosedNetwork.encoding.encode x.1.1.val) (List.replicate x.1.2.1.val true)
      (ResidualVertex.descriptorWord x.1.1.val x.1.2.1 x.2) [] [] []
      ((treeLabelEncoding s b arity).encode (literal s b arity x))) ![[],[],[]]
  change RunsExactly (TM2.step (program s b arity)) _ _ _ at run
  change TM2.step (program s b arity) _ = _ at ret
  simpa [Returning.cfg,ResidualVertex.phase,config,work,returns,literal,cfg,Nat.add_comm] using
    run.trans (runsExactly_one ret)

/-- Every retained input is erased by actual loops before clean halt. -/
theorem cleanup (raw vertex descriptor output : List Bool) :
    RunsExactly (TM2.step (program s b arity))
      (config s arity (.inr 9) [] [] raw vertex descriptor output [])
      (config s arity (.inr 12) [] [] [] [] [] output [])
      (raw.length+vertex.length+descriptor.length+3) := by
  have a := clear_exact (TM2.step (program s b arity)) rawKey (.inr 9) (.inr 10)
    (executesAt_tm2 _ _ _ rfl) () (work [] [] raw vertex descriptor output [])
  rw [update_raw] at a
  change RunsExactly _ (config s arity (.inr 9) [] [] raw vertex descriptor output [])
    (config s arity (.inr 10) [] [] [] vertex descriptor output []) (raw.length+1) at a
  have c := clear_exact (TM2.step (program s b arity)) vertexKey (.inr 10) (.inr 11)
    (executesAt_tm2 _ _ _ rfl) () (work [] [] [] vertex descriptor output [])
  rw [update_vertex] at c
  change RunsExactly _ (config s arity (.inr 10) [] [] [] vertex descriptor output [])
    (config s arity (.inr 11) [] [] [] [] descriptor output []) (vertex.length+1) at c
  have d := clear_exact (TM2.step (program s b arity)) descriptorKey (.inr 11) (.inr 12)
    (executesAt_tm2 _ _ _ rfl) () (work [] [] [] [] descriptor output [])
  rw [update_descriptor] at d
  change RunsExactly _ (config s arity (.inr 11) [] [] [] [] descriptor output [])
    (config s arity (.inr 12) [] [] [] [] [] output []) (descriptor.length+1) at d
  convert (a.trans c).trans d using 1
  omega

omit s b arity in
theorem work_empty : work [] [] [] [] [] [] [] = fun _ => [] := by decide

theorem initial (input : List Bool) :
    initList (machine s b arity).computer input = config s arity (.inr 0) input [] [] [] [] [] [] := by
  rw [BinaryCompose.Machine.init_eq]
  have h := update_input [] [] [] [] [] [] [] input
  rw [work_empty] at h
  change wordTape inputKey input = _ at h
  unfold config cfg
  congr 1

theorem halt_step (output : List Bool) :
    TM2.step (program s b arity) (config s arity (.inr 12) [] [] [] [] [] output []) =
      some (haltList (machine s b arity).computer output) := by
  rw [BinaryCompose.Machine.halt_eq]
  have h := update_output [] [] [] [] [] [] [] output
  rw [work_empty] at h
  change wordTape outputKey output = _ at h
  change some (⟨none,(none,()),work [] [] [] [] [] output []⟩ : Cfg Stack (Label s arity) Unit) = _
  rw [← h]

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualCoefficientInput
