import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualCoefficientInput

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualCoefficientInput
open Turing Computability StackProtocol BinaryCompose
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
set_option Elab.async false

@[simp] theorem update_input (input context raw vertex descriptor output temporary word : List Bool) :
    Function.update (work input context raw vertex descriptor output temporary) inputKey word =
      work word context raw vertex descriptor output temporary := by
  funext k; cases k with
  | inl k => cases k with
    | inl k => cases k with
      | inl k => fin_cases k <;> simp [work,ResidualVertex.work,ResidualVertex.tapes,VertexSignature.tapes,ListIndex.tapes,inputKey,contextKey,rawKey,vertexKey,descriptorKey,outputKey,temporaryKey,ResidualVertex.descriptorKey,ResidualVertex.outputKey,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]
      | inr k => fin_cases k <;> simp [work,ResidualVertex.work,ResidualVertex.tapes,VertexSignature.tapes,ListIndex.tapes,inputKey,contextKey,rawKey,vertexKey,descriptorKey,outputKey,temporaryKey,ResidualVertex.descriptorKey,ResidualVertex.outputKey,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]
    | inr k => fin_cases k <;> simp [work,ResidualVertex.work,ResidualVertex.tapes,VertexSignature.tapes,ListIndex.tapes,inputKey,contextKey,rawKey,vertexKey,descriptorKey,outputKey,temporaryKey,ResidualVertex.descriptorKey,ResidualVertex.outputKey,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]
  | inr k => fin_cases k <;> simp [work,ResidualVertex.work,ResidualVertex.tapes,VertexSignature.tapes,ListIndex.tapes,inputKey,contextKey,rawKey,vertexKey,descriptorKey,outputKey,temporaryKey,ResidualVertex.descriptorKey,ResidualVertex.outputKey,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]

@[simp] theorem update_context (input context raw vertex descriptor output temporary word : List Bool) :
    Function.update (work input context raw vertex descriptor output temporary) contextKey word =
      work input word raw vertex descriptor output temporary := by
  funext k; cases k with
  | inl k => cases k with
    | inl k => cases k with
      | inl k => fin_cases k <;> simp [work,ResidualVertex.work,ResidualVertex.tapes,VertexSignature.tapes,ListIndex.tapes,inputKey,contextKey,rawKey,vertexKey,descriptorKey,outputKey,temporaryKey,ResidualVertex.descriptorKey,ResidualVertex.outputKey,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]
      | inr k => fin_cases k <;> simp [work,ResidualVertex.work,ResidualVertex.tapes,VertexSignature.tapes,ListIndex.tapes,inputKey,contextKey,rawKey,vertexKey,descriptorKey,outputKey,temporaryKey,ResidualVertex.descriptorKey,ResidualVertex.outputKey,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]
    | inr k => fin_cases k <;> simp [work,ResidualVertex.work,ResidualVertex.tapes,VertexSignature.tapes,ListIndex.tapes,inputKey,contextKey,rawKey,vertexKey,descriptorKey,outputKey,temporaryKey,ResidualVertex.descriptorKey,ResidualVertex.outputKey,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]
  | inr k => fin_cases k <;> simp [work,ResidualVertex.work,ResidualVertex.tapes,VertexSignature.tapes,ListIndex.tapes,inputKey,contextKey,rawKey,vertexKey,descriptorKey,outputKey,temporaryKey,ResidualVertex.descriptorKey,ResidualVertex.outputKey,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]

@[simp] theorem update_raw (input context raw vertex descriptor output temporary word : List Bool) :
    Function.update (work input context raw vertex descriptor output temporary) rawKey word =
      work input context word vertex descriptor output temporary := by
  funext k; cases k with
  | inl k => cases k with
    | inl k => cases k with
      | inl k => fin_cases k <;> simp [work,ResidualVertex.work,ResidualVertex.tapes,VertexSignature.tapes,ListIndex.tapes,inputKey,contextKey,rawKey,vertexKey,descriptorKey,outputKey,temporaryKey,ResidualVertex.descriptorKey,ResidualVertex.outputKey,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]
      | inr k => fin_cases k <;> simp [work,ResidualVertex.work,ResidualVertex.tapes,VertexSignature.tapes,ListIndex.tapes,inputKey,contextKey,rawKey,vertexKey,descriptorKey,outputKey,temporaryKey,ResidualVertex.descriptorKey,ResidualVertex.outputKey,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]
    | inr k => fin_cases k <;> simp [work,ResidualVertex.work,ResidualVertex.tapes,VertexSignature.tapes,ListIndex.tapes,inputKey,contextKey,rawKey,vertexKey,descriptorKey,outputKey,temporaryKey,ResidualVertex.descriptorKey,ResidualVertex.outputKey,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]
  | inr k => fin_cases k <;> simp [work,ResidualVertex.work,ResidualVertex.tapes,VertexSignature.tapes,ListIndex.tapes,inputKey,contextKey,rawKey,vertexKey,descriptorKey,outputKey,temporaryKey,ResidualVertex.descriptorKey,ResidualVertex.outputKey,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]

@[simp] theorem update_vertex (input context raw vertex descriptor output temporary word : List Bool) :
    Function.update (work input context raw vertex descriptor output temporary) vertexKey word =
      work input context raw word descriptor output temporary := by
  funext k; cases k with
  | inl k => cases k with
    | inl k => cases k with
      | inl k => fin_cases k <;> simp [work,ResidualVertex.work,ResidualVertex.tapes,VertexSignature.tapes,ListIndex.tapes,inputKey,contextKey,rawKey,vertexKey,descriptorKey,outputKey,temporaryKey,ResidualVertex.descriptorKey,ResidualVertex.outputKey,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]
      | inr k => fin_cases k <;> simp [work,ResidualVertex.work,ResidualVertex.tapes,VertexSignature.tapes,ListIndex.tapes,inputKey,contextKey,rawKey,vertexKey,descriptorKey,outputKey,temporaryKey,ResidualVertex.descriptorKey,ResidualVertex.outputKey,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]
    | inr k => fin_cases k <;> simp [work,ResidualVertex.work,ResidualVertex.tapes,VertexSignature.tapes,ListIndex.tapes,inputKey,contextKey,rawKey,vertexKey,descriptorKey,outputKey,temporaryKey,ResidualVertex.descriptorKey,ResidualVertex.outputKey,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]
  | inr k => fin_cases k <;> simp [work,ResidualVertex.work,ResidualVertex.tapes,VertexSignature.tapes,ListIndex.tapes,inputKey,contextKey,rawKey,vertexKey,descriptorKey,outputKey,temporaryKey,ResidualVertex.descriptorKey,ResidualVertex.outputKey,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]

@[simp] theorem update_descriptor (input context raw vertex descriptor output temporary word : List Bool) :
    Function.update (work input context raw vertex descriptor output temporary) descriptorKey word =
      work input context raw vertex word output temporary := by
  funext k; cases k with
  | inl k => cases k with
    | inl k => cases k with
      | inl k => fin_cases k <;> simp [work,ResidualVertex.work,ResidualVertex.tapes,VertexSignature.tapes,ListIndex.tapes,inputKey,contextKey,rawKey,vertexKey,descriptorKey,outputKey,temporaryKey,ResidualVertex.descriptorKey,ResidualVertex.outputKey,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]
      | inr k => fin_cases k <;> simp [work,ResidualVertex.work,ResidualVertex.tapes,VertexSignature.tapes,ListIndex.tapes,inputKey,contextKey,rawKey,vertexKey,descriptorKey,outputKey,temporaryKey,ResidualVertex.descriptorKey,ResidualVertex.outputKey,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]
    | inr k => fin_cases k <;> simp [work,ResidualVertex.work,ResidualVertex.tapes,VertexSignature.tapes,ListIndex.tapes,inputKey,contextKey,rawKey,vertexKey,descriptorKey,outputKey,temporaryKey,ResidualVertex.descriptorKey,ResidualVertex.outputKey,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]
  | inr k => fin_cases k <;> simp [work,ResidualVertex.work,ResidualVertex.tapes,VertexSignature.tapes,ListIndex.tapes,inputKey,contextKey,rawKey,vertexKey,descriptorKey,outputKey,temporaryKey,ResidualVertex.descriptorKey,ResidualVertex.outputKey,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]

@[simp] theorem update_output (input context raw vertex descriptor output temporary word : List Bool) :
    Function.update (work input context raw vertex descriptor output temporary) outputKey word =
      work input context raw vertex descriptor word temporary := by
  funext k; cases k with
  | inl k => cases k with
    | inl k => cases k with
      | inl k => fin_cases k <;> simp [work,ResidualVertex.work,ResidualVertex.tapes,VertexSignature.tapes,ListIndex.tapes,inputKey,contextKey,rawKey,vertexKey,descriptorKey,outputKey,temporaryKey,ResidualVertex.descriptorKey,ResidualVertex.outputKey,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]
      | inr k => fin_cases k <;> simp [work,ResidualVertex.work,ResidualVertex.tapes,VertexSignature.tapes,ListIndex.tapes,inputKey,contextKey,rawKey,vertexKey,descriptorKey,outputKey,temporaryKey,ResidualVertex.descriptorKey,ResidualVertex.outputKey,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]
    | inr k => fin_cases k <;> simp [work,ResidualVertex.work,ResidualVertex.tapes,VertexSignature.tapes,ListIndex.tapes,inputKey,contextKey,rawKey,vertexKey,descriptorKey,outputKey,temporaryKey,ResidualVertex.descriptorKey,ResidualVertex.outputKey,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]
  | inr k => fin_cases k <;> simp [work,ResidualVertex.work,ResidualVertex.tapes,VertexSignature.tapes,ListIndex.tapes,inputKey,contextKey,rawKey,vertexKey,descriptorKey,outputKey,temporaryKey,ResidualVertex.descriptorKey,ResidualVertex.outputKey,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]

@[simp] theorem update_temporary (input context raw vertex descriptor output temporary word : List Bool) :
    Function.update (work input context raw vertex descriptor output temporary) temporaryKey word =
      work input context raw vertex descriptor output word := by
  funext k; cases k with
  | inl k => cases k with
    | inl k => cases k with
      | inl k => fin_cases k <;> simp [work,ResidualVertex.work,ResidualVertex.tapes,VertexSignature.tapes,ListIndex.tapes,inputKey,contextKey,rawKey,vertexKey,descriptorKey,outputKey,temporaryKey,ResidualVertex.descriptorKey,ResidualVertex.outputKey,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]
      | inr k => fin_cases k <;> simp [work,ResidualVertex.work,ResidualVertex.tapes,VertexSignature.tapes,ListIndex.tapes,inputKey,contextKey,rawKey,vertexKey,descriptorKey,outputKey,temporaryKey,ResidualVertex.descriptorKey,ResidualVertex.outputKey,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]
    | inr k => fin_cases k <;> simp [work,ResidualVertex.work,ResidualVertex.tapes,VertexSignature.tapes,ListIndex.tapes,inputKey,contextKey,rawKey,vertexKey,descriptorKey,outputKey,temporaryKey,ResidualVertex.descriptorKey,ResidualVertex.outputKey,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]
  | inr k => fin_cases k <;> simp [work,ResidualVertex.work,ResidualVertex.tapes,VertexSignature.tapes,ListIndex.tapes,inputKey,contextKey,rawKey,vertexKey,descriptorKey,outputKey,temporaryKey,ResidualVertex.descriptorKey,ResidualVertex.outputKey,Function.update,-Sum.elim_update_left,-Sum.update_elim_inl,-Sum.elim_update_right,-Sum.update_elim_inr]

variable (s b : ℕ) (arity : ℕ → ℕ)

/-- Unframe the retained original query, leaving the produced descriptor on the input stack. -/
theorem parse_context (context descriptor : List Bool) :
    RunsExactly (TM2.step (program s b arity))
      (config s arity (.inr 0) (Holant.Algebraic.frame context ++ descriptor) [] [] [] [] [] [])
      (config s arity (.inr 2) descriptor context [] [] [] [] []) (2 * (context.length+1)) := by
  have h := Frame.extract_exact inputKey contextKey temporaryKey (by decide) (by decide) (by decide)
    (TM2.step (program s b arity)) (.inr 0) (.inr 1) (.inr 2) (.inr 13)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) ()
    (work [] [] [] [] [] [] []) context descriptor []
  simpa only [config,tapes3,update_input,update_context,update_temporary,List.append_nil] using h

/-- Recover original raw bytes from the actual retained query field. -/
theorem parse_raw (raw suffix descriptor : List Bool) :
    RunsExactly (TM2.step (program s b arity))
      (config s arity (.inr 2) descriptor (Holant.Algebraic.frame raw ++ suffix) [] [] [] [] [])
      (config s arity (.inr 4) descriptor suffix raw [] [] [] []) (2 * (raw.length+1)) := by
  have h := Frame.extract_exact contextKey rawKey temporaryKey (by decide) (by decide) (by decide)
    (TM2.step (program s b arity)) (.inr 2) (.inr 3) (.inr 4) (.inr 13)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) ()
    (work descriptor [] [] [] [] [] []) raw suffix []
  simpa only [config,tapes3,update_context,update_raw,update_temporary,List.append_nil] using h

/-- Recover the physical original unary vertex ID without compact reindexing. -/
theorem parse_vertex (raw vertex edge descriptor : List Bool) :
    RunsExactly (TM2.step (program s b arity))
      (config s arity (.inr 4) descriptor (Holant.Algebraic.frame vertex ++ edge) raw [] [] [] [])
      (config s arity (.inr 6) descriptor edge raw vertex [] [] []) (2 * (vertex.length+1)) := by
  have h := Frame.extract_exact contextKey vertexKey temporaryKey (by decide) (by decide) (by decide)
    (TM2.step (program s b arity)) (.inr 4) (.inr 5) (.inr 6) (.inr 13)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) ()
    (work descriptor [] raw [] [] [] []) vertex edge []
  simpa only [config,tapes3,update_context,update_vertex,update_temporary,List.append_nil] using h

/-- The retained edge field is no longer needed and is explicitly erased. -/
theorem clear_edge (raw vertex edge descriptor : List Bool) :
    RunsExactly (TM2.step (program s b arity))
      (config s arity (.inr 6) descriptor edge raw vertex [] [] [])
      (config s arity (.inr 7) descriptor [] raw vertex [] [] []) (edge.length+1) := by
  have h := clear_exact (TM2.step (program s b arity)) contextKey (.inr 6) (.inr 7)
    (executesAt_tm2 _ _ _ rfl) () (work descriptor edge raw vertex [] [] [])
  rw [update_context] at h
  exact h

/-- Move exactly the physically produced descriptor into the actual fixed-family decoder. -/
theorem move_descriptor (raw vertex descriptor : List Bool) :
    RunsExactly (TM2.step (program s b arity))
      (config s arity (.inr 7) descriptor [] raw vertex [] [] [])
      (config s arity (.inl (ResidualVertex.sourceLabel s arity (.inr 0))) [] [] raw vertex descriptor [] [])
      (2 * (descriptor.length+1)) := by
  have h := Holant.OneHot.StackProgram.Machine.StackWord.move_exact inputKey descriptorKey temporaryKey
    (by decide) (by decide) (by decide) (TM2.step (program s b arity))
    (.inr 7) (.inr 8) (.inl (ResidualVertex.sourceLabel s arity (.inr 0)))
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) ()
    (work [] [] raw vertex [] [] []) descriptor []
  simpa only [config,tapes3,update_input,update_descriptor,update_temporary,List.append_nil] using h

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualCoefficientInput
