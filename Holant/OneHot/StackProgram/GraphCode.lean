import Holant.OneHot.StackProgram.GraphLabels
import Holant.OneHot.Computable.Evaluation.Components

/-! Finite-label instruction construction for actual residual trees, connected
components and their product. Original table/assignment labels survive each
restriction; interpretation is used only in the correctness proofs. -/

set_option backward.isDefEq.respectTransparency false

namespace Holant.OneHot.StackProgram

open Holant.OneHot.Computable.Evaluation Holant.OneHot.Decomposition
variable {A K : Type*}

/-- Interpret only labels, retaining all finite-network incidence data. -/
def interpretFiniteNetwork {V E : Type*} (coeff : A → K)
    (N : Holant.FiniteNetwork A V E 0) : Holant.FiniteNetwork K V E 0 where
  arity := N.arity
  ports := N.ports
  vertex v x := coeff (N.vertex v x)
  edge e x y := coeff (N.edge e x y)

/-- Increasing original-ID enumeration does not inspect coefficient values. -/
theorem interpret_orderedNetwork {V E : Type*} [Fintype V] [Fintype E]
    [LinearOrder V] [LinearOrder E] (coeff : A → K) (N : Holant.FiniteNetwork A V E 0) :
    interpretNetwork coeff N.orderedNetwork = (interpretFiniteNetwork coeff N).orderedNetwork := rfl

/-- Actual deleted-edge assignment insertion preserves literal table identities. -/
theorem interpret_conditionEdge {V E : Type*} [DecidableEq E]
    (coeff : A → K) (N : Holant.FiniteNetwork A V E 0) (e : E) (a b : Bool) :
    interpretFiniteNetwork coeff (N.executableConditionEdge e a b) =
      (interpretFiniteNetwork coeff N).executableConditionEdge e a b := rfl

/-- Original component restriction and reindexing are coefficient-independent. -/
theorem interpret_computedComponent (coeff : A → K) (N : Holant.Network A 0)
    (root : Fin N.shape.vertices) :
    interpretNetwork coeff (N.computedComponentNetwork root) =
      (interpretNetwork coeff N).computedComponentNetwork root := rfl

/-- Finite code with parents computed from actual original incidence. -/
def computedTreeCode (N : Holant.Network A 0) (zeroLabel : A)
    (root : Fin N.shape.vertices) (hc : N.incidenceGraph.Connected root) : Code A :=
  compileLabelTree (labelTree N zeroLabel (N.computedSpanning root hc) N.shape.vertices)

/-- The residual finite vertex/edge indices are enumerated in increasing order. -/
def computedFiniteTreeCode {V E : Type*} [Fintype V] [Fintype E]
    [LinearOrder V] [LinearOrder E] (N : Holant.FiniteNetwork A V E 0) (zeroLabel : A)
    (root : V) (hc : ∀ v, Relation.EqvGen (Link N.endpoint) root v) : Code A :=
  computedTreeCode N.orderedNetwork zeroLabel ((Fintype.orderIsoFinOfCardEq V rfl).symm root)
    (N.orderedNetwork_connected root hc)

/-- Both original occurrences are filled with their own selected bits before
labels are emitted; no physical pin or scalar gadget is added. -/
def conditionedCode (N : Holant.Network A 0) (zeroLabel : A)
    {root : Fin N.shape.vertices} (t : RootedSpanning N.shape.endpoint root)
    (e : t.Surplus) (a b : Bool) : Code A :=
  computedFiniteTreeCode (N.asFinite.executableConditionEdge e.1 a b) zeroLabel root
    (N.executableCondition_connected t e a b)

/-- Swap recovers the operand order used by the original arithmetic trace. -/
def addCode (left right : Code A) : Code A := left ++ right ++ [.swap, .add]
def mulCode (left right : Code A) : Code A := left ++ right ++ [.swap, .mul]

/-- Two actual residual codes and one addition, with the least computed surplus. -/
def computedUnicycleCode (N : Holant.Network A 0) (zeroLabel : A)
    (root : Fin N.shape.vertices) (hc : N.incidenceGraph.Connected root)
    (hcycle : N.shape.edges = N.shape.vertices) : Code A :=
  let t := N.computedSpanning root hc
  let e := surplusEdge t hcycle
  addCode (conditionedCode N zeroLabel t e false true)
    (conditionedCode N zeroLabel t e true false)

/-- Branch only on the original component's actual vertex/edge counts. -/
def computedConnectedCode (N : Holant.Network A 0) (zeroLabel : A)
    (root : Fin N.shape.vertices) (hc : N.incidenceGraph.Connected root) : Code A :=
  if hd : N.shape.vertices < N.shape.edges then [.zero]
  else if ht : N.shape.edges + 1 = N.shape.vertices then computedTreeCode N zeroLabel root hc
  else computedUnicycleCode N zeroLabel root hc (N.computed_cycle_count root hc hd ht)

variable [CommSemiring K]

theorem run_computedTreeCode (coeff : A → K) (N : Holant.Network A 0)
    (zeroLabel : A) (hz : coeff zeroLabel = 0)
    (root : Fin N.shape.vertices) (hc : N.incidenceGraph.Connected root) (suffix : List K) :
    run coeff (computedTreeCode N zeroLabel root hc) suffix =
      let p := (interpretNetwork coeff N).computedTreeProgram root hc
      some (p.run.1 :: suffix, p.values) :=
  run_labelTree coeff N zeroLabel hz (N.computedSpanning root hc) N.shape.vertices suffix

theorem run_computedFiniteTreeCode {V E : Type*} [Fintype V] [Fintype E]
    [LinearOrder V] [LinearOrder E] (coeff : A → K) (N : Holant.FiniteNetwork A V E 0)
    (zeroLabel : A) (hz : coeff zeroLabel = 0) (root : V)
    (hc : ∀ v, Relation.EqvGen (Link N.endpoint) root v) (suffix : List K) :
    run coeff (computedFiniteTreeCode N zeroLabel root hc) suffix =
      let p := (interpretFiniteNetwork coeff N).computedTreeProgram root hc
      some (p.run.1 :: suffix, p.values) :=
  run_computedTreeCode coeff N.orderedNetwork zeroLabel hz _ _ suffix

theorem run_conditionedCode (coeff : A → K) (N : Holant.Network A 0)
    (zeroLabel : A) (hz : coeff zeroLabel = 0)
    {root : Fin N.shape.vertices} (t : RootedSpanning N.shape.endpoint root)
    (e : t.Surplus) (a b : Bool) (suffix : List K) :
    run coeff (conditionedCode N zeroLabel t e a b) suffix =
      let p := (interpretNetwork coeff N).executableConditionedProgram t e a b
      some (p.run.1 :: suffix, p.values) :=
  run_computedFiniteTreeCode coeff (N.asFinite.executableConditionEdge e.1 a b)
    zeroLabel hz root _ suffix

/-- Composition identifies every ordered operand/result, not just the answer. -/
theorem run_addCode (coeff : A → K) (left right : Code A) (p q : Arithmetic K K)
    (hp : ∀ suffix, run coeff left suffix = some (p.run.1 :: suffix, p.values))
    (hq : ∀ suffix, run coeff right suffix = some (q.run.1 :: suffix, q.values))
    (suffix : List K) :
    run coeff (addCode left right) suffix =
      let r : Arithmetic K K := do
        let x ← p
        let y ← q
        Arithmetic.addOp x y
      some (r.run.1 :: suffix, r.values) := by
  simp [addCode, run_append, hp, hq, run, step, bind, Arithmetic.values_bind,
    Arithmetic.values_addOp, Arithmetic.run_bind, Arithmetic.run_addOp]

theorem run_mulCode (coeff : A → K) (left right : Code A) (p q : Arithmetic K K)
    (hp : ∀ suffix, run coeff left suffix = some (p.run.1 :: suffix, p.values))
    (hq : ∀ suffix, run coeff right suffix = some (q.run.1 :: suffix, q.values))
    (suffix : List K) :
    run coeff (mulCode left right) suffix =
      let r : Arithmetic K K := do
        let x ← p
        let y ← q
        Arithmetic.mulOp x y
      some (r.run.1 :: suffix, r.values) := by
  simp [mulCode, run_append, hp, hq, run, step, bind, Arithmetic.values_bind,
    Arithmetic.values_mulOp, Arithmetic.run_bind, Arithmetic.run_mulOp]

theorem run_computedUnicycleCode (coeff : A → K) (N : Holant.Network A 0)
    (zeroLabel : A) (hz : coeff zeroLabel = 0)
    (root : Fin N.shape.vertices) (hc : N.incidenceGraph.Connected root)
    (hcycle : N.shape.edges = N.shape.vertices) (suffix : List K) :
    run coeff (computedUnicycleCode N zeroLabel root hc hcycle) suffix =
      let p := (interpretNetwork coeff N).computedUnicycleProgram root hc hcycle
      some (p.run.1 :: suffix, p.values) := by
  exact run_addCode coeff _ _ _ _
    (run_conditionedCode coeff N zeroLabel hz _ _ false true)
    (run_conditionedCode coeff N zeroLabel hz _ _ true false) suffix

theorem run_computedConnectedCode (coeff : A → K) (N : Holant.Network A 0)
    (zeroLabel : A) (hz : coeff zeroLabel = 0)
    (root : Fin N.shape.vertices) (hc : N.incidenceGraph.Connected root) (suffix : List K) :
    run coeff (computedConnectedCode N zeroLabel root hc) suffix =
      let p := (interpretNetwork coeff N).computedConnectedProgram root hc
      some (p.run.1 :: suffix, p.values) := by
  unfold computedConnectedCode Holant.Network.computedConnectedProgram
  split
  · simp [interpretNetwork, *, run, step, Arithmetic.run_pure, Arithmetic.values_pure]
  · split
    · simpa [interpretNetwork, *] using run_computedTreeCode coeff N zeroLabel hz root hc suffix
    · simpa [interpretNetwork, *] using run_computedUnicycleCode coeff N zeroLabel hz root hc
        (N.computed_cycle_count root hc (by assumption) (by assumption)) suffix

/-- Retain the original labels after deterministic component restriction. -/
def computedComponentCode (N : Holant.Network A 0) (zeroLabel : A)
    (root : Fin N.shape.vertices) : Code A :=
  computedConnectedCode (N.computedComponentNetwork root) zeroLabel
    ((Fintype.orderIsoFinOfCardEq (N.incidenceGraph.Fiber root) rfl).symm (N.incidenceGraph.fiberRoot root))
    ((N.computedComponent root).orderedNetwork_connected _ (N.computedComponent_connected root))

theorem run_computedComponentCode (coeff : A → K) (N : Holant.Network A 0)
    (zeroLabel : A) (hz : coeff zeroLabel = 0)
    (root : Fin N.shape.vertices) (suffix : List K) :
    run coeff (computedComponentCode N zeroLabel root) suffix =
      let p := (interpretNetwork coeff N).computedComponentProgram root
      some (p.run.1 :: suffix, p.values) :=
  run_computedConnectedCode coeff (N.computedComponentNetwork root) zeroLabel hz _ _ suffix

/-- Each component code is emitted exactly once, and every product is an actual
stack instruction. The empty graph emits a literal one. -/
def finiteProductCode : {n : ℕ} → (Fin n → Code A) → Code A
  | 0, _ => [.one]
  | n + 1, p => mulCode (p 0) (finiteProductCode (fun i : Fin n => p i.succ))

theorem run_finiteProductCode {n : ℕ} (coeff : A → K) (codes : Fin n → Code A)
    (programs : Fin n → Arithmetic K K)
    (h : ∀ i suffix, run coeff (codes i) suffix =
      some ((programs i).run.1 :: suffix, (programs i).values))
    (suffix : List K) :
    run coeff (finiteProductCode codes) suffix =
      some ((Arithmetic.finiteProduct programs).run.1 :: suffix,
        (Arithmetic.finiteProduct programs).values) := by
  induction n generalizing suffix with
  | zero => simp [finiteProductCode, Arithmetic.finiteProduct, run, step,
      Arithmetic.run_pure, Arithmetic.values_pure]
  | succ n ih =>
    exact run_mulCode coeff _ _ _ _ (h 0)
      (fun suffix => ih (fun i => codes i.succ) (fun i => programs i.succ)
        (fun i => h i.succ) suffix) suffix

/-- The complete finite-label graph program is constructed before any arithmetic
interpretation, from actually computed original component roots. -/
def computedGraphCode (N : Holant.Network A 0) (zeroLabel : A) : Code A :=
  finiteProductCode (fun i : Fin (Fintype.card N.ComputedRoot) =>
    computedComponentCode N zeroLabel (N.computedRootOrder i).1)

/-- Exact full arithmetic trace of the complete arbitrary-graph code, including
all residual evaluations and component multiplication. -/
theorem run_computedGraphCode (coeff : A → K) (N : Holant.Network A 0)
    (zeroLabel : A) (hz : coeff zeroLabel = 0) (suffix : List K) :
    run coeff (computedGraphCode N zeroLabel) suffix =
      let p := (interpretNetwork coeff N).computedOneHotProgram
      some (p.run.1 :: suffix, p.values) :=
  run_finiteProductCode coeff _ _
    (fun i => run_computedComponentCode coeff N zeroLabel hz (N.computedRootOrder i).1) suffix

end Holant.OneHot.StackProgram

namespace Holant.Complexity.RawClosedNetwork

open Holant.OneHot Holant.OneHot.StackProgram
open Holant.Complexity.ExactSignatureTables

variable {s b : ℕ} {arity : ℕ → ℕ} (r : RawClosedNetwork)

/-- Full graph syntax reads only actual fixed table-entry identities and ordered
assignments, including residual conditioning and all connected components. -/
def labelledGraphCode (h : r.WellFormed s b arity) : Code (TreeLabel s b arity) :=
  computedGraphCode (r.labelNetwork h) none

/-- Exact whole-program trace correspondence with the bounded executable graph
arithmetic program. No noncomputable choice of equivalent coefficient is used. -/
theorem run_labelledGraphCode {K : Type*} [CommSemiring K]
    (h : r.WellFormed s b arity) (coeff : CoefficientIndex s b arity → K) (suffix : List K) :
    run (interpretLabel coeff) (r.labelledGraphCode h) suffix =
      let p := (r.executableRealize h (fun i x => coeff (.inl ⟨i, x⟩))
        (fun i x y => coeff (.inr (i, x, y)))).computedOneHotProgram
      some (p.run.1 :: suffix, p.values) :=
  run_computedGraphCode (interpretLabel coeff) (r.labelNetwork h) none rfl suffix

/-- Exact native-X one-hot value on the original arbitrary multigraph, including
empty input, nullary vertices, loops, parallel edges and dense components. -/
theorem labelledGraphCode_denote {K : Type*} [CommSemiring K]
    (h : r.WellFormed s b arity) (coeff : CoefficientIndex s b arity → K)
    (hf : ∀ i, Holant.Signature.OneHot (fun x => coeff (.inl ⟨i, x⟩)))
    (hX : ∀ i, (fun x y => coeff (.inr (i, x, y))) = Holant.Signature.disequality)
    (suffix : List K) :
    (run (interpretLabel coeff) (r.labelledGraphCode h) suffix).map Prod.fst =
      some ((r.realize h (fun i x => coeff (.inl ⟨i, x⟩))
        (fun i x y => coeff (.inr (i, x, y)))).denote Fin.elim0 :: suffix) := by
  rw [run_labelledGraphCode]
  simp only [Option.map_some]
  have hs := (r.executableRealize h (fun i x => coeff (.inl ⟨i, x⟩))
    (fun i x y => coeff (.inr (i, x, y)))).computedOneHotProgram_spec
      (fun v => hf (r.signatureLabel h v)) (fun e => hX (r.edgeLabel h e))
  rw [hs.1, r.executableRealize_eq]

end Holant.Complexity.RawClosedNetwork

namespace Holant.OneHot.StackProgram

open Holant.Complexity

/-- Actual validated Boolean graph words become actual finite instruction lists,
without a field value or arithmetic continuation among the inputs. -/
def compileGraphBits (s b : ℕ) (arity : ℕ → ℕ) (bits : List Bool) :
    Option (Code (RawClosedNetwork.TreeLabel s b arity)) :=
  ((RawClosedNetwork.validatedEncoding s b arity).decode bits).map fun r =>
    r.1.labelledGraphCode r.2

@[simp] theorem compileGraphBits_encode {s b : ℕ} {arity : ℕ → ℕ}
    (r : RawClosedNetwork) (h : r.WellFormed s b arity) :
    compileGraphBits s b arity (RawClosedNetwork.encoding.encode r) =
      some (r.labelledGraphCode h) := by
  unfold compileGraphBits
  have hd := (RawClosedNetwork.validatedEncoding s b arity).decode_encode ⟨r, h⟩
  change (RawClosedNetwork.validatedEncoding s b arity).decode
    (RawClosedNetwork.encoding.encode r) = some ⟨r, h⟩ at hd
  rw [hd]
  rfl

end Holant.OneHot.StackProgram
