import Holant.Complexity.GraphPreprocessing.ComponentSelection.RootEntry
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RawParentTable

/-! Raw graph bytes to the exact increasing list of original component roots.
The canonical table is computed inside the finite machine; the list scan emits
precisely its parent-none rows, with a physical empty-list terminator. -/
namespace Holant.Complexity.GraphPreprocessing.ComponentSelection.RawRoots
open Turing Computability BinaryCompose FixedFieldMachines OriginalCoefficient
open Holant.OneHot.Computable
open Holant.OneHot.StackProgram.GraphLabelEncoding
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false
variable {s b : ℕ} {arity : ℕ → ℕ}

def rowsValue (rows : List Graph.ParentRow) : List ℕ :=
  (rows.filter fun r => decide (r.parent=none)).map Graph.ParentRow.component
abbrev outputEncoding := framedListEncoding UnaryBinary.unaryEncoding
def contextEncoding := ContextFlatMap.inputEncoding Frame.wordEncoding (fun _ => ParentRowEncoding.row)
def chunk (x : Σ _ : List Bool, Graph.ParentRow) : List Bool := RootEntry.value x.2
noncomputable def chunkComputes : Computes (sigmaEncoding Frame.wordEncoding (fun _ => ParentRowEncoding.row))
    Frame.wordEncoding chunk :=
  recode ((Wiring.secondComputes Frame.wordEncoding ParentRowEncoding.row).andThen RootEntry.computes)
    (fun x => (x.1,x.2)) (fun _ => rfl) (fun _ => rfl)
noncomputable def contextComputes : Computes ParentRowEncoding.table contextEncoding
    (fun rows => ⟨[],rows⟩) :=
  recode (pairComputes (constantComputes ParentRowEncoding.table Frame.wordEncoding [])
    (identityComputes ParentRowEncoding.table)) id (fun _ => rfl) (fun _ => rfl)
noncomputable def chunksComputes : Computes ParentRowEncoding.table Frame.wordEncoding
    (fun rows => rows.flatMap RootEntry.value) :=
  (contextComputes.andThen (ContextFlatMap.computes Frame.wordEncoding (fun _ => ParentRowEncoding.row) chunk chunkComputes))
theorem chunks_word (rows : List Graph.ParentRow) :
    rows.flatMap RootEntry.value++[false]=outputEncoding.encode (rowsValue rows) := by
  induction rows with
  | nil => rfl
  | cons r rows ih =>
    by_cases hp : r.parent=none
    · simp [RootEntry.value,hp,rowsValue,framedListEncoding,framedListEncode,List.append_assoc] at ih ⊢
      exact congrArg (fun tail => Holant.Algebraic.frame (List.replicate r.component true)++tail) ih
    · simpa [RootEntry.value,hp,rowsValue,framedListEncoding,framedListEncode] using ih
noncomputable def tableComputes : Computes ParentRowEncoding.table outputEncoding rowsValue :=
  recode ((pairComputes chunksComputes (constantComputes ParentRowEncoding.table Frame.wordEncoding [false])).andThen
    WordJoin.computes) id (fun _ => rfl) chunks_word

abbrev chunkMachine : Machine := secondMachine.compose RootEntry.machine
abbrev contextMachine : Machine := pairMachine (Constant.machine []) identityMachine
abbrev chunksMachine : Machine := contextMachine.compose (ContextFlatMap.machine chunkMachine)
abbrev tableMachine : Machine := (pairMachine chunksMachine (Constant.machine [false])).compose WordJoin.machine
@[simp] theorem tableComputes_machine : tableComputes.machine=tableMachine := rfl

theorem rows_original (g : Graph) : rowsValue g.parentTable=g.roots.map Fin.val := by
  have general (vs : List g.Vertex) : rowsValue (vs.map g.parentRow)=
      (vs.filter fun v => decide (g.label v=v)).map Fin.val := by
    induction vs with
    | nil => rfl
    | cons v vs ih =>
      by_cases hp : (g.parentRow v).parent=none
      · have hv := (g.parentRow_none_iff v).mp hp
        simpa [rowsValue,hp,hv,Graph.parentRow_component] using congrArg (List.cons v.val) ih
      · have hv : g.label v≠v := fun h => hp ((g.parentRow_none_iff v).mpr h)
        simpa [rowsValue,hp,hv] using ih
  exact general (List.finRange g.vertices)
abbrev Input (s b : ℕ) (arity : ℕ → ℕ) := RawParentTable.Input s b arity
def value (x : Input s b arity) := (x.val.graph x.property).roots.map Fin.val
abbrev machine : Machine := RawParentTable.machine.compose tableMachine
noncomputable def computes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (RawClosedNetwork.validatedEncoding s b arity) outputEncoding value :=
  congrComputes ((RawParentTable.computes s b arity).andThen tableComputes)
    (fun x => rows_original (x.val.graph x.property))
@[simp] theorem computes_machine (s b : ℕ) (arity : ℕ → ℕ) : (computes s b arity).machine=machine := rfl
theorem inFP : InFP (RawClosedNetwork.validatedEncoding s b arity) outputEncoding value := (computes s b arity).inFP
noncomputable def timePolynomial (s b : ℕ) (arity : ℕ → ℕ) : Polynomial ℕ := (computes s b arity).time
noncomputable def timed (x : Input s b arity) :
    TM2OutputsInTime machine.computer (RawClosedNetwork.encoding.encode x.val)
      (some (outputEncoding.encode (value x)))
      ((timePolynomial s b arity).eval (RawClosedNetwork.encoding.encode x.val).length) := (computes s b arity).outputs x
noncomputable def primitivePolynomial (s b : ℕ) (arity : ℕ → ℕ) : Polynomial ℕ :=
  timePolynomial s b arity*Polynomial.C machine.primitiveBudget
theorem primitive_bound (x : Input s b arity) :
    primitiveCost machine (timed x).steps (some (initList machine.computer (RawClosedNetwork.encoding.encode x.val)))≤
      (primitivePolynomial s b arity).eval (RawClosedNetwork.encoding.encode x.val).length := by
  have h := Nat.mul_le_mul_right machine.primitiveBudget (timed x).steps_le_m
  simpa only [primitivePolynomial,Polynomial.eval_mul,Polynomial.eval_C] using le_trans (primitiveCost_le _ _ _) h
end Holant.Complexity.GraphPreprocessing.ComponentSelection.RawRoots
