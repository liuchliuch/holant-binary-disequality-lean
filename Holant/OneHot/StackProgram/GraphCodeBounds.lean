import Holant.OneHot.StackProgram.GraphCode
import Holant.OneHot.StackProgram.GraphLabelEncoding

/-! Linear instruction/serialized-code size of the actual original-graph
compiler. This counts concrete emitted syntax, not the size of a denotationally
equal surrogate. Intermediate scalar sizes remain a separate obligation. -/

namespace Holant.OneHot.StackProgram

open Holant.OneHot.Computable.Evaluation Holant.OneHot.Decomposition
variable {A K : Type*} [CommSemiring K]

theorem length_compileLabelTree_le (coeff : A → K) (q : Tree A) :
    (compileLabelTree q).length ≤ 5 * (interpretTree coeff q).closedProgram.run.2 := by
  cases q with
  | node a b ts =>
    simp only [compileLabelTree, length_compileClosed, interpretTree, Tree.closedProgram,
      Forest.closedProgram_run, interpretForest_vertices, interpretForest_edges]
    omega

theorem length_computedTreeCode_le (coeff : A → K) (N : Holant.Network A 0)
    (zeroLabel : A) (hz : coeff zeroLabel = 0)
    (root : Fin N.shape.vertices) (hc : N.incidenceGraph.Connected root) :
    (computedTreeCode N zeroLabel root hc).length ≤
      5 * ((interpretNetwork coeff N).computedTreeProgram root hc).run.2 := by
  have h := length_compileLabelTree_le coeff
    (labelTree N zeroLabel (N.computedSpanning root hc) N.shape.vertices)
  rw [interpret_labelTree coeff N zeroLabel hz] at h
  exact h

theorem length_computedFiniteTreeCode_le {V E : Type*} [Fintype V] [Fintype E]
    [LinearOrder V] [LinearOrder E] (coeff : A → K) (N : Holant.FiniteNetwork A V E 0)
    (zeroLabel : A) (hz : coeff zeroLabel = 0) (root : V)
    (hc : ∀ v, Relation.EqvGen (Link N.endpoint) root v) :
    (computedFiniteTreeCode N zeroLabel root hc).length ≤
      5 * ((interpretFiniteNetwork coeff N).computedTreeProgram root hc).run.2 :=
  length_computedTreeCode_le coeff N.orderedNetwork zeroLabel hz _ _

theorem length_conditionedCode_le (coeff : A → K) (N : Holant.Network A 0)
    (zeroLabel : A) (hz : coeff zeroLabel = 0)
    {root : Fin N.shape.vertices} (t : RootedSpanning N.shape.endpoint root)
    (e : t.Surplus) (a b : Bool) :
    (conditionedCode N zeroLabel t e a b).length ≤
      5 * ((interpretNetwork coeff N).executableConditionedProgram t e a b).run.2 :=
  length_computedFiniteTreeCode_le coeff (N.asFinite.executableConditionEdge e.1 a b)
    zeroLabel hz root _

theorem length_computedUnicycleCode_le (coeff : A → K) (N : Holant.Network A 0)
    (zeroLabel : A) (hz : coeff zeroLabel = 0)
    (root : Fin N.shape.vertices) (hc : N.incidenceGraph.Connected root)
    (hcycle : N.shape.edges = N.shape.vertices) :
    (computedUnicycleCode N zeroLabel root hc hcycle).length ≤
      5 * ((interpretNetwork coeff N).computedUnicycleProgram root hc hcycle).run.2 := by
  let t := N.computedSpanning root hc
  let e := surplusEdge t hcycle
  have hl := length_conditionedCode_le coeff N zeroLabel hz t e false true
  have hr := length_conditionedCode_le coeff N zeroLabel hz t e true false
  change (addCode _ _).length ≤ _
  simp only [addCode, List.length_append, List.length_cons, List.length_nil,
    Holant.Network.computedUnicycleProgram, Holant.Network.executableSpanningUnicycleProgram,
    bind, Arithmetic.run_bind, Arithmetic.run_addOp]
  change (conditionedCode N zeroLabel t e false true).length +
      (conditionedCode N zeroLabel t e true false).length + 2 ≤
    5 * (((interpretNetwork coeff N).executableConditionedProgram t e false true).run.2 +
      (((interpretNetwork coeff N).executableConditionedProgram t e true false).run.2 + 1))
  omega

theorem length_computedConnectedCode_le (coeff : A → K) (N : Holant.Network A 0)
    (zeroLabel : A) (hz : coeff zeroLabel = 0)
    (root : Fin N.shape.vertices) (hc : N.incidenceGraph.Connected root) :
    (computedConnectedCode N zeroLabel root hc).length ≤
      5 * ((interpretNetwork coeff N).computedConnectedProgram root hc).run.2 + 1 := by
  unfold computedConnectedCode Holant.Network.computedConnectedProgram
  split
  · simp [interpretNetwork, *, Arithmetic.run_pure]
  · split
    · have h := length_computedTreeCode_le coeff N zeroLabel hz root hc
      simpa [interpretNetwork, *] using (Nat.le_add_right_of_le h : _ ≤ _ + 1)
    · have h := length_computedUnicycleCode_le coeff N zeroLabel hz root hc
        (N.computed_cycle_count root hc (by assumption) (by assumption))
      simpa [interpretNetwork, *] using (Nat.le_add_right_of_le h : _ ≤ _ + 1)

theorem length_computedComponentCode_le (coeff : A → K) (N : Holant.Network A 0)
    (zeroLabel : A) (hz : coeff zeroLabel = 0) (root : Fin N.shape.vertices) :
    (computedComponentCode N zeroLabel root).length ≤
      5 * ((interpretNetwork coeff N).computedComponentProgram root).run.2 + 1 :=
  length_computedConnectedCode_le coeff (N.computedComponentNetwork root) zeroLabel hz _ _

theorem length_finiteProductCode_le {n : ℕ} (codes : Fin n → Code A)
    (programs : Fin n → Arithmetic K K)
    (h : ∀ i, (codes i).length ≤ 5 * (programs i).run.2 + 1) :
    (finiteProductCode codes).length ≤ 5 * (Arithmetic.finiteProduct programs).run.2 + 1 := by
  induction n with
  | zero => simp [finiteProductCode, Arithmetic.finiteProduct, Arithmetic.run_pure]
  | succ n ih =>
    have h0 := h 0
    have ht := ih (fun i => codes i.succ) (fun i => programs i.succ) (fun i => h i.succ)
    simp only [finiteProductCode, mulCode, List.length_append, List.length_cons, List.length_nil,
      Arithmetic.finiteProduct, bind, Arithmetic.run_bind, Arithmetic.run_mulOp]
    omega

theorem length_computedGraphCode_le (coeff : A → K) (N : Holant.Network A 0)
    (zeroLabel : A) (hz : coeff zeroLabel = 0) :
    (computedGraphCode N zeroLabel).length ≤
      5 * (interpretNetwork coeff N).computedOneHotProgram.run.2 + 1 :=
  length_finiteProductCode_le _ _
    (fun i => length_computedComponentCode_le coeff N zeroLabel hz (N.computedRootOrder i).1)

/-- The code-size estimate uses the proved actual component arithmetic bound. -/
theorem length_computedGraphCode_le_graph (coeff : A → K) (N : Holant.Network A 0)
    (zeroLabel : A) (hz : coeff zeroLabel = 0)
    (hf : ∀ v, Holant.Signature.OneHot (fun x => coeff (N.vertex v x)))
    (hX : ∀ e, (fun x y => coeff (N.edge e x y)) = Holant.Signature.disequality) :
    (computedGraphCode N zeroLabel).length ≤ 55 * (N.shape.vertices + N.shape.edges) + 1 := by
  have h := length_computedGraphCode_le coeff N zeroLabel hz
  have hp := ((interpretNetwork coeff N).computedOneHotProgram_spec hf hX).2
  change _ ≤ 11 * (N.shape.vertices + N.shape.edges) at hp
  omega

end Holant.OneHot.StackProgram

namespace Holant.Complexity.RawClosedNetwork

open Holant.OneHot Holant.OneHot.StackProgram
open Holant.OneHot.StackProgram.GraphLabelEncoding
open Holant.Complexity.ExactSignatureTables

variable {s b : ℕ} {arity : ℕ → ℕ} (r : RawClosedNetwork)

/-- Count concrete finite opcodes in the actually generated original-graph code. -/
theorem labelledGraphCode_length_le {K : Type*} [CommSemiring K]
    (h : r.WellFormed s b arity) (coeff : CoefficientIndex s b arity → K)
    (hf : ∀ i, Holant.Signature.OneHot (fun x => coeff (.inl ⟨i, x⟩)))
    (hX : ∀ i, (fun x y => coeff (.inr (i, x, y))) = Holant.Signature.disequality) :
    (r.labelledGraphCode h).length ≤ 55 * (r.vertices.length + r.edges.length) + 1 :=
  length_computedGraphCode_le_graph (interpretLabel coeff) (r.labelNetwork h) none rfl
    (fun v => hf (r.signatureLabel h v)) (fun e => hX (r.edgeLabel h e))

/-- All opcode tags, literal original assignments and framing bits are counted.
The multiplier is fixed by the finite signature family before any graph input. -/
theorem labelledGraphCode_encoded_length_le {K : Type*} [CommSemiring K]
    (h : r.WellFormed s b arity) (coeff : CoefficientIndex s b arity → K)
    (hf : ∀ i, Holant.Signature.OneHot (fun x => coeff (.inl ⟨i, x⟩)))
    (hX : ∀ i, (fun x y => coeff (.inr (i, x, y))) = Holant.Signature.disequality) :
    ((codeEncoding (treeLabelEncoding s b arity)).encode (r.labelledGraphCode h)).length ≤
      (2 * lengthBound s b arity + 14) *
        (55 * (RawClosedNetwork.encoding.encode r).length + 1) + 1 := by
  have hc := r.labelledGraphCode_length_le h coeff hf hX
  have hs := r.decoded_counts_le_input_length h
  change r.vertices.length + r.edges.length ≤ (RawClosedNetwork.encoding.encode r).length at hs
  have he := codeEncoding_length_le (treeLabelEncoding s b arity) (lengthBound s b arity)
    (treeLabelEncoding_length_le s b arity) (r.labelledGraphCode h)
  have hn : (r.labelledGraphCode h).length ≤
      55 * (RawClosedNetwork.encoding.encode r).length + 1 := by omega
  exact he.trans (Nat.add_le_add_right
    (Nat.mul_le_mul_left (2 * lengthBound s b arity + 14) hn) 1)

end Holant.Complexity.RawClosedNetwork

namespace Holant.OneHot.StackProgram

open Holant.Complexity GraphLabelEncoding

/-- Original graph bytes to actual finite opcode bytes, without semantic field
values in code generation. This is a data function, not a timed machine theorem. -/
def compileSerializedGraph (s b : ℕ) (arity : ℕ → ℕ) (bits : List Bool) : Option (List Bool) :=
  (compileGraphBits s b arity bits).map (codeEncoding (treeLabelEncoding s b arity)).encode

@[simp] theorem compileSerializedGraph_encode {s b : ℕ} {arity : ℕ → ℕ}
    (r : RawClosedNetwork) (h : r.WellFormed s b arity) :
    compileSerializedGraph s b arity (RawClosedNetwork.encoding.encode r) =
      some ((codeEncoding (treeLabelEncoding s b arity)).encode (r.labelledGraphCode h)) := by
  simp [compileSerializedGraph, compileGraphBits_encode r h]

end Holant.OneHot.StackProgram
