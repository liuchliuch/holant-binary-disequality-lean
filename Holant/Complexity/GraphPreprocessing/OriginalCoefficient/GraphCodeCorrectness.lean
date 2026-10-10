import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.GraphListCompiler
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ComponentCodeCorrectness
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.GraphRootOrder

/-! The actual raw-input finite machine emits the established labelledGraphCode
literally. This preserves every instruction and all ordered arithmetic trace
values before choosing any fixed field interpretation. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.GraphCodeCorrectness
open Turing Computability BinaryCompose FixedFieldMachines
open Holant.OneHot Holant.OneHot.Computable Holant.OneHot.StackProgram
open Holant.OneHot.StackProgram.GraphLabelEncoding
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 1500000
set_option Elab.async false
variable {s b : ℕ} {arity : ℕ → ℕ}

theorem entries (x : GraphListCompiler.Input s b arity) :
    GraphListCompiler.entries x=(x.val.labelNetwork x.property).incidenceGraph.roots.map
      (computedComponentCode (x.val.labelNetwork x.property) none) := by
  change ((x.val.graph x.property).roots.map (fun v => ComponentCodeCompiler.value ⟨x,v⟩))=
    (x.val.graph x.property).roots.map (computedComponentCode (x.val.labelNetwork x.property) none)
  apply List.map_congr_left
  intro v hv
  exact ComponentCodeCorrectness.value_at_root ⟨x,v⟩ ((x.val.graph x.property).mem_roots v |>.mp hv)

theorem value (x : GraphListCompiler.Input s b arity) :
    GraphListCompiler.value x=x.val.labelledGraphCode x.property := by
  change CodeProduct.product (GraphListCompiler.entries x)=computedGraphCode (x.val.labelNetwork x.property) none
  rw [entries]
  exact GraphRootOrder.product_components (x.val.labelNetwork x.property) none

/-- Exact source-level compiler witness; no prepared table, tree, code or size
certificate is part of the input. -/
noncomputable def computes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (RawClosedNetwork.validatedEncoding s b arity) (codeEncoding (treeLabelEncoding s b arity))
      (fun x => x.val.labelledGraphCode x.property) :=
  congrComputes (GraphListCompiler.computes s b arity) value
@[simp] theorem computes_machine (s b : ℕ) (arity : ℕ → ℕ) :
    (computes s b arity).machine=GraphListCompiler.machine s b arity := rfl
@[simp] theorem computes_time (s b : ℕ) (arity : ℕ → ℕ) :
    (computes s b arity).time=(GraphListCompiler.computes s b arity).time := rfl
theorem inFP : InFP (RawClosedNetwork.validatedEncoding s b arity) (codeEncoding (treeLabelEncoding s b arity))
    (fun x => x.val.labelledGraphCode x.property) := (computes s b arity).inFP

/-- Full ordered arithmetic-trace equality follows from the actual emitted code,
for any coefficient interpretation; no final-value-only replacement is used. -/
theorem trace {K : Type} [CommSemiring K] (x : GraphListCompiler.Input s b arity)
    (coeff : ExactSignatureTables.CoefficientIndex s b arity → K) (suffix : List K) :
    run (RawClosedNetwork.interpretLabel coeff) (GraphListCompiler.value x) suffix=
      let p := (x.val.executableRealize x.property (fun i a => coeff (.inl ⟨i,a⟩))
        (fun i a b => coeff (.inr (i,a,b)))).computedOneHotProgram
      some (p.run.1::suffix,p.values) := by
  rw [value]
  exact x.val.run_labelledGraphCode x.property coeff suffix
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.GraphCodeCorrectness
