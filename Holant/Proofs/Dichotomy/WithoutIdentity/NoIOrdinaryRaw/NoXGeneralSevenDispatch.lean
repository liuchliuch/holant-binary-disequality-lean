import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalRankThreeOddRepairSource
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoXGeneralSevenShiftAnti
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.GenericOrdinarySource
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoXWeightedAntiResourcesOriginal
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.Target

/-! Every real shifted odd-seven source is consumed. Canonical support keeps
its actual row, the dual noncode support uses the physical two-copy repair,
and every remaining shift supplies the proved actual anti hardness source. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIOrdinaryRaw.NoXGeneralSevenDispatch
open Holant Holant.Tractable
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace D
export OrdinaryNegativeXUniversalResource (OddResource AlphaResource AffineResource)
end D
namespace P
export NoXGeneralSevenShiftPlan (classIndex representative same_support nonDual_iff_index)
export NoXReciprocalMixedProjectionCore (logical)
export OrdinaryNegativeSparseMixingAlpha (codeSeven)
end P
namespace C
export NoXReciprocalRankThreeOddRepairCore (Exotic exotic canonical_iff)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
set_option Elab.async false
section Geometry
variable {K : IntermediateField ℚ AlgebraicComplex} {s : ℕ} {b : ℕ→ℕ}
variable (H : (j : Fin s)→Signature K (b j.val)) (row : D.OddResource (s:=s) b 7)
variable (sign : Fin 7→Bool)
variable (support : ∀z,row.ambient H z≠0 ↔ ∃x : Fin 3→Bool,P.logical sign z=P.codeSeven x)
include support in
theorem canonical_full (zero : P.classIndex sign=0) (x : Fin 3→Bool) :
    row.ambient H (P.codeSeven x)≠0 := by
  apply (support _).mpr
  apply (P.same_support sign _).mpr
  rw [zero]
  refine ⟨x,?_⟩
  funext i
  fin_cases i <;> simp [P.logical,P.representative]
include support in
theorem exotic_support (seven : P.classIndex sign=7) (z : Fin 7→Bool) :
    row.ambient H z≠0 ↔ C.Exotic z := by
  rw [support,P.same_support sign z,seven]
  change (∃x : Fin 3→Bool,P.logical C.exotic z=P.codeSeven x) ↔ C.Exotic z
  exact (C.canonical_iff _).symm
end Geometry

variable {s : ℕ} {a : ℕ→ℕ}
variable (G : NoIOrdinaryRaw.Target)
variable (src : NoIOrdinaryRaw.GenericOrdinarySource.Data G)
local instance : Algebra ℚ src.K:=src.K.algebra'
variable (row : D.OddResource (s:=src.size) src.b 7) (sign : Fin 7→Bool)
variable (support : ∀z,row.ambient src.H z≠0 ↔ ∃x : Fin 3→Bool,P.logical sign z=P.codeSeven x)
variable (negative : StableHigherCurrentOrdinaryTerminal.Obstruction (preprocess (NoIOrdinaryRaw.GenericOrdinarySource.family G src)))
include support negative in
theorem ordinary (alpha : Affine ((OrdinaryNegativeOcticCommonBasis.basis true).symm.action (row.ambient src.H))) :
    NoIOrdinaryRaw.NoXWeightedAntiResourcesOriginal.Hard G ∨ Nonempty (D.AlphaResource src.H .seven) := by
  classical
  by_cases zero : P.classIndex sign=0
  · right
    exact ⟨{toOddResource:=row,alpha:=alpha,full:=canonical_full src.H row sign support zero}⟩
  · by_cases seven : P.classIndex sign=7
    · right
      exact ⟨NoXReciprocalRankThreeOddRepairSource.alphaResource src.H (src.p false) (src.hp false)
        row (exotic_support src.H row sign support seven) alpha⟩
    · exact Or.inl (NoIOrdinaryRaw.NoXGeneralSevenShiftAnti.countingHard G src row sign support
        ((P.nonDual_iff_index sign).mpr ⟨zero,seven⟩) negative)
include support negative in
theorem uniform (affine : Affine (row.ambient src.H)) :
    NoIOrdinaryRaw.NoXWeightedAntiResourcesOriginal.Hard G ∨ Nonempty (D.AffineResource src.H .seven) := by
  classical
  by_cases zero : P.classIndex sign=0
  · right
    exact ⟨{toOddResource:=row,affine:=affine,full:=canonical_full src.H row sign support zero}⟩
  · by_cases seven : P.classIndex sign=7
    · right
      exact ⟨NoXReciprocalRankThreeOddRepairSource.affineResource src.H (src.p false) (src.hp false)
        row (exotic_support src.H row sign support seven) affine⟩
    · exact Or.inl (NoIOrdinaryRaw.NoXGeneralSevenShiftAnti.countingHard G src row sign support
        ((P.nonDual_iff_index sign).mpr ⟨zero,seven⟩) negative)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIOrdinaryRaw.NoXGeneralSevenDispatch
end
