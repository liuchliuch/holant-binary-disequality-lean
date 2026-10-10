import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ComponentCodeCompiler
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualExpansionInterchange
import Holant.Complexity.GraphPreprocessing.ComponentSelection.GraphCorrespondence

/-! Exact literal GraphCode identity for the fully physical component compiler.
Classification, original cut selection and both residual branches are derived
from the actual raw input, with complete opcode order retained. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ComponentCodeCorrectness
open Turing Computability BinaryCompose FixedFieldMachines ComponentSelection
open Holant.OneHot Holant.OneHot.Computable Holant.OneHot.Computable.Evaluation
open Holant.OneHot.StackProgram Holant.OneHot.StackProgram.GraphLabelEncoding
open CanonicalStability CanonicalExpansion ResidualExpansion
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 1500000
set_option Elab.async false
variable {s b : ℕ} {arity : ℕ → ℕ}

theorem classify_canonical (x : RawComponentInputs.Input s b arity) :
    RawSurplus.value x.val=classification (x.val.1.val.labelNetwork x.val.1.property).incidenceGraph x.val.2 := by
  change classify ((surplusEdges (x.val.1.val.graph x.val.1.property)
    ((x.val.1.val.graph x.val.1.property).label x.val.2)).map Fin.val)=_
  rw [x.property]
  rfl

theorem select_cycle_none (x : RawComponentInputs.Input s b arity) (kind : Classification)
    (h : RawSurplus.value x.val=kind) (hk : kind=.tree ∨ kind=.dense) : RawComponentInputs.selectCycle x=none := by
  rcases hk with rfl | rfl <;>
    unfold RawComponentInputs.selectCycle <;> split <;> simp_all

theorem select_cycle_some (x : RawComponentInputs.Input s b arity) (e : ℕ)
    (h : RawSurplus.value x.val=.unicycle e) :
    RawComponentInputs.selectCycle x=some (RawComponentInputs.mkCycle x e h) := by
  unfold RawComponentInputs.selectCycle
  split <;> simp_all
  rename_i e' heq
  have he : e'=e := Classification.unicycle.inj (heq.symm.trans h)
  subst e'
  rfl

theorem canonical_value (x : RawComponentInputs.Input s b arity) :
    ComponentCodeCompiler.canonicalValue x=
      computedComponentCode (x.val.1.val.labelNetwork x.val.1.property) none x.val.2 := by
  let N := x.val.1.val.labelNetwork x.val.1.property
  let root := x.val.2
  let C := N.computedComponentNetwork root
  have hr : N.incidenceGraph.label root=root := x.property
  change ComponentCodeCompiler.canonicalValue x=computedConnectedCode C none (componentRoot N root) (component_connected N root)
  by_cases hd : C.shape.vertices<C.shape.edges
  · rw [computedConnectedCode,dif_pos hd]
    have hclass : RawSurplus.value x.val=.dense := by
      rw [classify_canonical]
      exact (component_scan_dense_iff N root hr).mpr hd
    have ht : RawComponentInputs.selectTree x=none := by simp [RawComponentInputs.selectTree,hclass]
    have hc := select_cycle_none x .dense hclass (Or.inr rfl)
    simp [ComponentCodeCompiler.canonicalValue,ht,hc]
  · rw [computedConnectedCode,dif_neg hd]
    by_cases ht : C.shape.edges+1=C.shape.vertices
    · rw [dif_pos ht]
      have hclass : RawSurplus.value x.val=.tree := by
        rw [classify_canonical]
        exact (component_scan_tree_iff N root hr).mpr ht
      have hs : RawComponentInputs.selectTree x=some x := by simp [RawComponentInputs.selectTree,hclass]
      simp only [ComponentCodeCompiler.canonicalValue,hs,Option.map_some,Option.getD_some]
      rfl
    · rw [dif_neg ht]
      let hc := C.computed_cycle_count (componentRoot N root) (component_connected N root) hd ht
      let cut : (componentTree N root).Surplus := surplusEdge (componentTree N root) hc
      have hclass : RawSurplus.value x.val=.unicycle (componentOriginalEdge N root cut.val).val := by
        rw [classify_canonical]
        exact component_scan_unicycle_selected N root hr hc
      let q := RawComponentInputs.mkCycle x (componentOriginalEdge N root cut.val).val hclass
      have hq : (network q.val.1).incidenceGraph.label q.val.2=q.val.2 := q.property.1
      have hcut : componentOriginalEdge (network q.val.1) q.val.2 cut.val=ResidualContext.edge q.val.1 := by
        apply Fin.ext
        rfl
      have hs : RawComponentInputs.selectTree x=none := by simp [RawComponentInputs.selectTree,hclass]
      have hsel : RawComponentInputs.selectCycle x=some q := select_cycle_some x _ hclass
      simp only [ComponentCodeCompiler.canonicalValue,hs,hsel,Option.map_none,Option.getD_none,Option.map_some,Option.getD_some]
      change addCode (JoinedResidualCompiler.branchValue false true q) (JoinedResidualCompiler.branchValue true false q)=
        addCode (conditionedCode C none (componentTree N root) cut false true) (conditionedCode C none (componentTree N root) cut true false)
      congr 1
      · exact code_interchange q.val.1 q.val.2 cut false true hq hcut
      · exact code_interchange q.val.1 q.val.2 cut true false hq hcut

@[simp] theorem normalized_canonical (x : RawComponentInputs.Input s b arity) : RawComponentCompiler.normalized x.val=x := by
  apply Subtype.ext
  simp only [RawComponentCompiler.normalized]
  change (⟨x.val.1,(x.val.1.val.graph x.val.1.property).label x.val.2⟩ : RawRootReach.Input s b arity)=x.val
  rw [x.property]

theorem value_at_root (x : RawRootReach.Input s b arity) (h : (x.1.val.graph x.1.property).label x.2=x.2) :
    ComponentCodeCompiler.value x=computedComponentCode (x.1.val.labelNetwork x.1.property) none x.2 := by
  have he := normalized_canonical (⟨x,h⟩ : RawComponentInputs.Input s b arity)
  change ComponentCodeCompiler.canonicalValue (RawComponentCompiler.normalized x)=_
  rw [he]
  exact canonical_value ⟨x,h⟩
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ComponentCodeCorrectness
