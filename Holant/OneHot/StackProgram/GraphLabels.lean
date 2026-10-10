import Holant.OneHot.StackProgram.Tree
import Holant.OneHot.Computable.Evaluation.RawTree
import Holant.Complexity.EncodedHolantOutputSize

/-!
# Original coefficient labels in executable graph trees

The tree is built on literal labels before interpreting the coefficient table.
No field-value search, equality test, or choice of a representation occurs in
code generation. The interpretation theorem identifies the whole emitted tree,
and therefore the exact ordered arithmetic trace, not just its final value.
-/

namespace Holant.OneHot.StackProgram

open Holant.OneHot.Computable.Evaluation Holant.OneHot.Decomposition

variable {A K : Type*}

theorem interpret_ofList {ι : Type*} (coeff : A → K) (port : ι → A)
    (trees : ι → Tree A) (xs : List ι) :
    interpretForest coeff (Summary.ofList port trees xs) =
      Summary.ofList (fun i => coeff (port i)) (fun i => interpretTree coeff (trees i)) xs := by
  induction xs with
  | nil => rfl
  | cons i xs ih => simp only [Summary.ofList, interpretForest, ih]

variable {n m : ℕ} {endpoint : Fin m → Bool → Fin n} {root : Fin n}

/-- Literal finite-index construction commutes with any coefficient map; no
algebraic structure or homomorphism condition is required on the label type. -/
theorem interpret_build (t : RootedSpanning endpoint root) (coeff : A → K)
    (a b : Fin n → A) (port : {u : Fin n // u ≠ root} → A) (fuel : ℕ) (v : Fin n) :
    interpretTree coeff (build t a b port fuel v) =
      build t (fun u => coeff (a u)) (fun u => coeff (b u))
        (fun u => coeff (port u)) fuel v := by
  induction fuel generalizing v with
  | zero => rfl
  | succ fuel ih =>
    simp only [build, interpretTree, interpret_ofList, ih]

/-- Interpretation preserves the exact original shape, local port order, and
both endpoint orientations. -/
def interpretNetwork (coeff : A → K) (N : Holant.Network A 0) : Holant.Network K 0 where
  shape := N.shape
  vertex v x := coeff (N.vertex v x)
  edge e x y := coeff (N.edge e x y)

/-- Actual input labels are selected at the original zero/singleton assignments.
The one extra label is the unused parent coefficient at the root. -/
def labelTree (N : Holant.Network A 0) (zeroLabel : A)
    {r : Fin N.shape.vertices} (t : RootedSpanning N.shape.endpoint r)
    (maxDepth : ℕ) : Tree A :=
  tree t (fun v => N.vertex v (fun _ => false))
    (fun v => if h : v = r then zeroLabel else
      N.vertex (N.shape.closedPorts.symm (t.parentEnd ⟨v, h⟩)).1
        (fun j => decide (j = (N.shape.closedPorts.symm (t.parentEnd ⟨v, h⟩)).2)))
    (fun u => N.vertex (N.shape.closedPorts.symm ((t.parentEnd u).1, !(t.parentEnd u).2)).1
      (fun j => decide (j =
        (N.shape.closedPorts.symm ((t.parentEnd u).1, !(t.parentEnd u).2)).2))) maxDepth

variable [CommSemiring K]

/-- Whole syntax equality gives, in particular, equality of all intermediate
operands and results of the actual compiled program. -/
theorem interpret_labelTree (coeff : A → K) (N : Holant.Network A 0)
    (zeroLabel : A) (hz : coeff zeroLabel = 0)
    {r : Fin N.shape.vertices} (t : RootedSpanning N.shape.endpoint r) (maxDepth : ℕ) :
    interpretTree coeff (labelTree N zeroLabel t maxDepth) =
      (interpretNetwork coeff N).executableTree t maxDepth := by
  unfold labelTree Holant.Network.executableTree tree
  rw [interpret_build]
  congr 1
  funext v
  unfold Holant.Network.executableParent
  split <;> simp_all [interpretNetwork, Holant.Network.occurrenceCoefficient]
  rfl

/-- Closed compilation discards the unused root-parent label exactly as the
existing closed arithmetic program does. -/
def compileLabelTree (q : Tree A) : Code A :=
  match q with
  | .node a _ ts => compileClosed a ts

/-- The entire output stack and arithmetic trace of the label-generated code
are those of the actual original-network executable tree. -/
theorem run_compileLabelTree (coeff : A → K) (q : Tree A) (suffix : List K) :
    run coeff (compileLabelTree q) suffix =
      some ((interpretTree coeff q).closedProgram.run.1 :: suffix,
        (interpretTree coeff q).closedProgram.values) := by
  cases q with
  | node a b ts => exact run_compileClosed coeff a ts suffix

theorem run_labelTree (coeff : A → K) (N : Holant.Network A 0)
    (zeroLabel : A) (hz : coeff zeroLabel = 0)
    {r : Fin N.shape.vertices} (t : RootedSpanning N.shape.endpoint r) (maxDepth : ℕ)
    (suffix : List K) :
    run coeff (compileLabelTree (labelTree N zeroLabel t maxDepth)) suffix =
      some (((interpretNetwork coeff N).executableTree t maxDepth).closedProgram.run.1 :: suffix,
        ((interpretNetwork coeff N).executableTree t maxDepth).closedProgram.values) := by
  rw [run_compileLabelTree, interpret_labelTree coeff N zeroLabel hz]

end Holant.OneHot.StackProgram

namespace Holant.Complexity.RawClosedNetwork

open Holant.OneHot Holant.OneHot.StackProgram Holant.OneHot.Computable
open Holant.Complexity.ExactSignatureTables

variable {s b : ℕ} {arity : ℕ → ℕ} (r : RawClosedNetwork)

/-- A fixed finite alphabet: original table-entry identities and one zero label.
Its size depends only on the fixed signature family, never on the input graph. -/
abbrev TreeLabel (s b : ℕ) (arity : ℕ → ℕ) :=
  Option (CoefficientIndex s b arity)

/-- Read the literal signature/edge label and ordered local assignment. This uses
the executable original inverse-incidence lookup, with no semantic coefficient. -/
def labelNetwork (h : r.WellFormed s b arity) : Holant.Network (TreeLabel s b arity) 0 :=
  r.executableRealize h (fun i x => some (.inl ⟨i, x⟩))
    (fun i x y => some (.inr (i, x, y)))

/-- Zero is a dedicated instruction-table entry, not inferred by testing values. -/
def interpretLabel {K : Type*} [Zero K] (coeff : CoefficientIndex s b arity → K) :
    TreeLabel s b arity → K
  | none => 0
  | some a => coeff a

@[simp] theorem interpret_labelNetwork {K : Type*} [Zero K]
    (h : r.WellFormed s b arity) (coeff : CoefficientIndex s b arity → K) :
    interpretNetwork (interpretLabel coeff) (r.labelNetwork h) =
      r.executableRealize h (fun i x => coeff (.inl ⟨i, x⟩))
        (fun i x y => coeff (.inr (i, x, y))) := rfl

/-- Direct code generation from original input labels and computed parent edges.
The full fixed-field table is absent from the runtime inputs of this definition. -/
def labelledTree (h : r.WellFormed s b arity) (root : Fin r.vertices.length)
    (hc : (r.graph h).Connected root) : Tree (TreeLabel s b arity) :=
  labelTree (r.labelNetwork h) none (r.executableSpanning h root hc) r.vertices.length

/-- Literal whole syntax, hence all arithmetic trace entries, specializes to the
actual executable original-network tree under the fixed coefficient table. -/
theorem interpret_labelledTree {K : Type*} [CommSemiring K]
    (h : r.WellFormed s b arity) (coeff : CoefficientIndex s b arity → K)
    (root : Fin r.vertices.length) (hc : (r.graph h).Connected root) :
    interpretTree (interpretLabel coeff) (r.labelledTree h root hc) =
      r.executableTree h (fun i x => coeff (.inl ⟨i, x⟩))
        (fun i x y => coeff (.inr (i, x, y))) root hc := by
  exact interpret_labelTree (interpretLabel coeff) (r.labelNetwork h) none rfl
    (r.executableSpanning h root hc) r.vertices.length

/-- The finite serialized instruction syntax is produced before arithmetic. -/
def labelledTreeCode (h : r.WellFormed s b arity) (root : Fin r.vertices.length)
    (hc : (r.graph h).Connected root) : Code (TreeLabel s b arity) :=
  compileLabelTree (r.labelledTree h root hc)

/-- The complete ordered trace agrees with the already bounded actual program;
this is stronger than replacing it with any evaluator having the same answer. -/
theorem run_labelledTreeCode {K : Type*} [CommSemiring K]
    (h : r.WellFormed s b arity) (coeff : CoefficientIndex s b arity → K)
    (root : Fin r.vertices.length) (hc : (r.graph h).Connected root) (suffix : List K) :
    run (interpretLabel coeff) (r.labelledTreeCode h root hc) suffix =
      let q := r.executableTree h (fun i x => coeff (.inl ⟨i, x⟩))
        (fun i x y => coeff (.inr (i, x, y))) root hc
      some (q.closedProgram.run.1 :: suffix, q.closedProgram.values) := by
  unfold labelledTreeCode
  rw [run_compileLabelTree, interpret_labelledTree]

/-- Original-network correctness for the actually emitted code and every
preserved stack suffix, with the original one-hot/native-X hypotheses. -/
theorem labelledTreeCode_denote {K : Type*} [CommSemiring K]
    (h : r.WellFormed s b arity) (coeff : CoefficientIndex s b arity → K)
    (root : Fin r.vertices.length) (hc : (r.graph h).Connected root)
    (ht : r.edges.length + 1 = r.vertices.length)
    (hf : ∀ i, Holant.Signature.OneHot (fun x => coeff (.inl ⟨i, x⟩)))
    (hX : ∀ i, (fun x y => coeff (.inr (i, x, y))) = Holant.Signature.disequality)
    (suffix : List K) :
    (run (interpretLabel coeff) (r.labelledTreeCode h root hc) suffix).map Prod.fst =
      some ((r.realize h (fun i x => coeff (.inl ⟨i, x⟩))
        (fun i x y => coeff (.inr (i, x, y)))).denote Fin.elim0 :: suffix) := by
  rw [run_labelledTreeCode]
  simp only [Option.map_some]
  rw [r.executableTree_program_spec h _ _ root hc ht hf hX]

/-- Total finite-label compilation, rejecting empty, disconnected and non-tree
records by the same executed predicates as the arithmetic data compiler. -/
def compileLabelledTree (h : r.WellFormed s b arity) : Option (Code (TreeLabel s b arity)) :=
  if hn : 0 < r.vertices.length then
    let root : Fin r.vertices.length := ⟨0, hn⟩
    if hc : (r.graph h).Connected root then
      if r.edges.length + 1 = r.vertices.length then
        some (r.labelledTreeCode h root hc)
      else none
    else none
  else none

/-- Successful compilation has the original assignment-sum semantics. -/
theorem compileLabelledTree_denote {K : Type*} [CommSemiring K]
    (h : r.WellFormed s b arity) (coeff : CoefficientIndex s b arity → K)
    (hf : ∀ i, Holant.Signature.OneHot (fun x => coeff (.inl ⟨i, x⟩)))
    (hX : ∀ i, (fun x y => coeff (.inr (i, x, y))) = Holant.Signature.disequality)
    (code : Code (TreeLabel s b arity)) (hc : r.compileLabelledTree h = some code)
    (suffix : List K) :
    (run (interpretLabel coeff) code suffix).map Prod.fst =
      some ((r.realize h (fun i x => coeff (.inl ⟨i, x⟩))
        (fun i x y => coeff (.inr (i, x, y)))).denote Fin.elim0 :: suffix) := by
  unfold compileLabelledTree at hc
  split at hc
  · dsimp only at hc
    split at hc
    · split at hc
      · cases Option.some.inj hc
        exact r.labelledTreeCode_denote h coeff _ _ (by assumption) hf hX suffix
      · contradiction
    · contradiction
  · contradiction

end Holant.Complexity.RawClosedNetwork

namespace Holant.OneHot.StackProgram

open Holant.Complexity

/-- Actual Boolean graph input to finite coefficient-labelled code. Fixed field
values are not an argument; every literal records an original table entry. -/
def compileLabelledTreeBits (s b : ℕ) (arity : ℕ → ℕ) (bits : List Bool) :
    Option (Code (RawClosedNetwork.TreeLabel s b arity)) :=
  ((RawClosedNetwork.validatedEncoding s b arity).decode bits).bind fun r =>
    r.1.compileLabelledTree r.2

theorem compileLabelledTreeBits_encode {s b : ℕ} {arity : ℕ → ℕ}
    (r : RawClosedNetwork) (h : r.WellFormed s b arity) :
    compileLabelledTreeBits s b arity (RawClosedNetwork.encoding.encode r) =
      r.compileLabelledTree h := by
  unfold compileLabelledTreeBits
  have hd := (RawClosedNetwork.validatedEncoding s b arity).decode_encode ⟨r, h⟩
  change (RawClosedNetwork.validatedEncoding s b arity).decode
    (RawClosedNetwork.encoding.encode r) = some ⟨r, h⟩ at hd
  rw [hd]
  rfl

end Holant.OneHot.StackProgram
