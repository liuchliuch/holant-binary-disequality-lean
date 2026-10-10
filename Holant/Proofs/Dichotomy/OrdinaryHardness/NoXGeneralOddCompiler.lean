import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralOddLabels
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralOddRawValue
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralOddCellValue
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXOrdinaryGraphAdjoin

/-! An arbitrary original-table odd-boundary/even-private recipe is an actual
ordinary macro using only its original labels, Eq4 and the two retained pins.
Temporary boundary markers are replaced by Eq4 terminals before the output
is formed; the final signature is exactly the original resource's trace. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralOddCompiler
open Holant Holant.Tractable Holant.Complexity
open Holant.LocalDrafts.TetrahedralCompletion.EvenCSPReduction
open OrdinaryNegativeCubicGadgets
namespace L
export NoXGeneralOddLayout (source eqLiteral network markerFactor marker_get mark Remaining vertices unary)
export NoXGeneralOddLabels (labels literal ones)
end L
namespace T
export NoXGeneralOddTerminalNetwork (graph markerEdge value)
end T
namespace R
export NoXGeneralOddRawValue (sourceInput sourceVariable conditional)
end R
namespace C
export Holant.LocalDrafts.TetrahedralCompletion.EvenCSPReduction.Compilation
  (cell edgeIndex sourceNetwork portEnumeration original_ordered_port original_route Words flatWords bits Supported supported_bits)
end C
namespace D
export OrdinaryNegativeXUniversalResource (OddResource)
end D
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
attribute [local instance] Classical.propDecidable
variable {K : IntermediateField ℚ AlgebraicComplex} {s n : ℕ} {a : ℕ→ℕ}
variable (H : (i : Fin s)→Signature K (a i.val)) (e p0 p1 : Fin s)
variable (he : (⟨a e.val,H e⟩ : AnySignature K)=⟨4,Holant.EightVertex.ProductAnchor.equalityFour⟩)
variable (h0 : (⟨a p0.val,H p0⟩ : AnySignature K)=⟨1,Holant.LocalDrafts.RemoteWork.CountingBridge.Gates.pin false⟩)
variable (h1 : (⟨a p1.val,H p1⟩ : AnySignature K)=⟨1,Holant.LocalDrafts.RemoteWork.CountingBridge.Gates.pin true⟩)
variable (row : D.OddResource (s:=s) a n)

abbrev src := L.source p0 p1 (congrArg Sigma.fst h0) (congrArg Sigma.fst h1) row
abbrev net := L.network H e p0 p1 he (congrArg Sigma.fst h0) (congrArg Sigma.fst h1) row
abbrev vertices := L.vertices H e p0 p1 he (congrArg Sigma.fst h0) (congrArg Sigma.fst h1) row
abbrev unary := L.unary H e p0 p1 he (congrArg Sigma.fst h0) (congrArg Sigma.fst h1) row
abbrev labels := L.labels H e p0 p1 he (congrArg Sigma.fst h0) (congrArg Sigma.fst h1) row
abbrev literal := L.literal H e p0 p1 he (congrArg Sigma.fst h0) (congrArg Sigma.fst h1) row

local instance remainingFintype : Fintype (L.Remaining H e p0 p1 he (congrArg Sigma.fst h0) (congrArg Sigma.fst h1) row) := by
  unfold L.Remaining
  infer_instance

def graph : Macro H n := by
  letI := remainingFintype H e p0 p1 he h0 h1 row
  exact T.graph (K:=K) (V:=L.Remaining H e p0 p1 he (congrArg Sigma.fst h0) (congrArg Sigma.fst h1) row)
    (net H e p0 p1 he h0 h1 row) (vertices H e p0 p1 he h0 h1 row)
    (unary H e p0 p1 he h0 h1 row) H (labels H e p0 p1 he h0 h1 row) (literal H e p0 p1 he h0 h1 row) e he

def markedPort (j : Fin n) : (src H p0 p1 h0 h1 row).val.Ports :=
  ⟨L.markerFactor p0 p1 (congrArg Sigma.fst h0) (congrArg Sigma.fst h1) row j,
    ⟨0,by rw [L.marker_get];simp⟩⟩

theorem marked_route (j : Fin n) : Raw.route (src H p0 p1 h0 h1 row) (markedPort H p0 p1 h0 h1 row j)=
    R.sourceVariable H row p0 p1 h0 h1 j := by
  apply Fin.ext
  have hx:=L.marker_get p0 p1 (congrArg Sigma.fst h0) (congrArg Sigma.fst h1) row j
  have bound : 0<((src H p0 p1 h0 h1 row).val.factors.get
      (L.markerFactor p0 p1 (congrArg Sigma.fst h0) (congrArg Sigma.fst h1) row j)).2.length := by
    rw [hx]
    simp
  have hv:=congrArg (fun f : Factor=>f.2.getD 0 0) hx
  change ((src H p0 p1 h0 h1 row).val.factors.get
    (L.markerFactor p0 p1 (congrArg Sigma.fst h0) (congrArg Sigma.fst h1) row j)).2.getD 0 0=j.val+2 at hv
  rw [List.getD_eq_getElem _ _ bound] at hv
  exact hv

theorem port_exact (j : Fin n) :
    (⟨vertices H e p0 p1 he h0 h1 row (.inr j),Fin.cast (unary H e p0 p1 he h0 h1 row j).symm 0⟩ :
      Σv : Fin (net H e p0 p1 he h0 h1 row).shape.vertices,Fin ((net H e p0 p1 he h0 h1 row).shape.arity v))=
      (C.portEnumeration (src H p0 p1 h0 h1 row)).symm (.inl (markedPort H p0 p1 h0 h1 row j)) := by
  rw [C.original_ordered_port]
  apply Sigma.ext rfl
  apply heq_of_eq
  exact Fin.ext rfl

theorem selected_bits (w : C.Words (src H p0 p1 h0 h1 row))
    (supported : C.Supported (src H p0 p1 h0 h1 row) w) (j : Fin n) :
    C.flatWords (src H p0 p1 h0 h1 row) w
      (T.markerEdge (net H e p0 p1 he h0 h1 row) (vertices H e p0 p1 he h0 h1 row)
        (unary H e p0 p1 he h0 h1 row) j)=
      w (R.sourceVariable H row p0 p1 h0 h1 j) (C.cell (src H p0 p1 h0 h1 row) (R.sourceVariable H row p0 p1 h0 h1 j)).root := by
  have bits : C.flatWords (src H p0 p1 h0 h1 row) w
      (T.markerEdge (net H e p0 p1 he h0 h1 row) (vertices H e p0 p1 he h0 h1 row)
        (unary H e p0 p1 he h0 h1 row) j)=C.bits (src H p0 p1 h0 h1 row) w (markedPort H p0 p1 h0 h1 row j) := by
    unfold T.markerEdge
    erw [port_exact,C.original_route]
    simp only [src,C.flatWords,C.bits,Equiv.coe_fn_mk,Cells.Cell.boundary]
    erw [Equiv.symm_apply_apply]
  have supportedBits:=C.supported_bits (src H p0 p1 h0 h1 row) w supported (markedPort H p0 p1 h0 h1 row j)
  have changed:=congrArg (fun q : Fin (src H p0 p1 h0 h1 row).val.variables=>
    w q (C.cell (src H p0 p1 h0 h1 row) q).root) (marked_route H p0 p1 h0 h1 row j)
  exact bits.trans (supportedBits.trans changed)

theorem value (x : Fin n→Bool) : (graph H e p0 p1 he h0 h1 row).network.denote x=row.signature H x := by
  let := remainingFintype H e p0 p1 he h0 h1 row
  rw [graph,T.value _ _ _ _ _ _ _ _
    (L.ones H e p0 p1 he (congrArg Sigma.fst h0) (congrArg Sigma.fst h1) row)]
  have cell:=NoXGeneralOddCellValue.value (NoXGeneralOddTable.table H) (NoXGeneralOddTable.old e)
    (L.eqLiteral H e he) (src H p0 p1 h0 h1 row)
    (T.markerEdge (net H e p0 p1 he h0 h1 row) (vertices H e p0 p1 he h0 h1 row)
      (unary H e p0 p1 he h0 h1 row))
    (R.sourceVariable H row p0 p1 h0 h1) (selected_bits H e p0 p1 he h0 h1 row) x
  exact cell.trans (R.conditional H row p0 p1 h0 h1 x)

def output : NoXOrdinaryGraphAdjoin.Output H n where
  network:=(graph H e p0 p1 he h0 h1 row).network
  labels:=(graph H e p0 p1 he h0 h1 row).labels
  exact:=(graph H e p0 p1 he h0 h1 row).exact
  ordinary:=(graph H e p0 p1 he h0 h1 row).edges

theorem output_value : (output H e p0 p1 he h0 h1 row).network.denote=row.signature H :=
  funext (value H e p0 p1 he h0 h1 row)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralOddCompiler
end
