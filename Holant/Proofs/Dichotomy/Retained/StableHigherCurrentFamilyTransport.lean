import Holant.Proofs.Dichotomy.Retained.StableHigherCurrentPurePinsCore
import Holant.Proofs.Closure.ClosureSourceRows

/-! Exact family image transport from the old current-palette row source to
its finite-table interpreter. The actual anchor and its coordinate data are
preserved, with no field descent or computational-pin premise. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableHigherCurrentFamilyTransport
open Holant Holant.Tractable Holant.Complexity
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G)

/-- The row source and finite-table interpreter use exactly the same current
family, including every current label. This is only a change of family syntax. -/
theorem ambientFamily_eq : ClosureSourceRows.ambientFamily G P =
    UniversalPairReduction.FiniteFamily.family (StableHigherCurrentPurePinsCore.mapped G P) := by
  ext f
  constructor
  · rintro ⟨g,⟨i,rfl⟩,rfl⟩
    exact ⟨i,rfl⟩
  · rintro ⟨i,rfl⟩
    exact ⟨⟨P.arity i.val,P.table i⟩,⟨i,rfl⟩,rfl⟩

/-- Retain the exact anchor signature, basis, edge scale and vertex scale;
only its actual graph's family membership is rewritten. -/
def fromAmbient (A : QuaternaryEqualityTerminal.AnchorStep
    (ClosureSourceRows.ambientFamily G P)) : QuaternaryEqualityTerminal.AnchorStep
      (UniversalPairReduction.FiniteFamily.family (StableHigherCurrentPurePinsCore.mapped G P)) where
  signature := A.signature
  basis := A.basis
  edgeScale := A.edgeScale
  vertexScale := A.vertexScale
  edge_ne_zero := A.edge_ne_zero
  vertex_ne_zero := A.vertex_ne_zero
  actual := by rw [← ambientFamily_eq G P]; exact A.actual
  edge_exact := A.edge_exact
  anchor_exact := A.anchor_exact

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableHigherCurrentFamilyTransport
end
