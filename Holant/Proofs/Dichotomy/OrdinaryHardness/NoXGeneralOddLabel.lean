import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeXUniversalResource

/-! Literal source labels as actual odd recipes; no new dictionary entry. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralOddLabel
open Holant Holant.Tractable
open OrdinaryNegativeMixedBlockData
namespace D
export OrdinaryNegativeXUniversalResource (OddResource)
end D
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
set_option Elab.async false
variable {s : ℕ} {b : ℕ→ℕ} (j : Fin s)
def rows : Recipe (u:=1) (s:=s) (a:=fun _=>b j.val+0) (b:=b) :=
  fun _=>[⟨j,fun q=>.inr (Fin.castAdd 0 q)⟩]

def resource : D.OddResource (s:=s) b (b j.val) where
  privateCount := 0
  rows := rows j
  constant_even bit := by
    simp [rows,ports,Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionPhaseOccurrences.count_ofFn]
  boundary_odd q := by
    simp [rows,ports,Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionPhaseOccurrences.count_ofFn]
  private_even q := Fin.elim0 q

variable {K : IntermediateField ℚ AlgebraicComplex}
variable (H : (j : Fin s)→Signature K (b j.val))
theorem value (x : Fin (b j.val)→Bool) : (resource j).signature H x=H j x := by
  change OrdinaryNegativeMixedBlockSource.trace H 0 (rows j) 0 x=_
  rw [OrdinaryNegativeSparseMixingSource.trace_zero]
  simp [coefficient,Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyBundleValue.coefficient,rows]

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralOddLabel
end
