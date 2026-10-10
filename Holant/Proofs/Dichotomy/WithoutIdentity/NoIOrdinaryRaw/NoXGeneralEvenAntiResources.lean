import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoXGeneralEvenAntiBinary
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralEvenAntiClosed
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralEvenAntiNonclosed
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoXNonproduct
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.GenericOrdinarySource
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoXWeightedAntiResourcesOriginal
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.Target

/-! Arbitrary actual non-Affine/non-Product even resources and a full anti
even resource give original-oracle hardness. Support closure and every fixed
extraction gadget are selected internally; no anti graph label is assumed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIOrdinaryRaw.NoXGeneralEvenAntiResources
open Holant Holant.Tractable
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace B
export OrdinaryNegativeSparseMixingSource (Block)
export OrdinaryNegativeXUniversalResource (EvenBad)
end B
namespace C
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEONegativeClosedSupport (Closed)
end C
namespace A
export NoXGeneralEvenAntiClosed (binary binary_nonaffine binary_nonproduct)
end A
namespace N
export NoXGeneralEvenAntiNonclosed (binary binary_nonaffine binary_nonproduct)
end N
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
variable {s m n : ℕ} {a : ℕ→ℕ}
variable (G : NoIOrdinaryRaw.Target)
variable (src : NoIOrdinaryRaw.GenericOrdinarySource.Data G)
local instance : Algebra ℚ src.K := src.K.algebra'
variable (first : B.Block (s:=src.size) (b:=src.b) m) (second : B.Block (s:=src.size) (b:=src.b) n)
variable (antiRow : B.Block (s:=src.size) (b:=src.b) 2)
variable (v w : src.K) (hv : v≠0) (hw : w≠0)
variable (anti : antiRow.signature src.H=NoXWeightedAntiSigned.anti v w)
variable (nonaffine : ¬Affine (fun x=>(first.signature src.H x : AlgebraicComplex)))
variable (nonproduct : ¬Product (fun x=>(second.signature src.H x : AlgebraicComplex)))

include hv hw anti nonaffine nonproduct in
theorem countingHard : NoIOrdinaryRaw.NoXWeightedAntiResourcesOriginal.Hard G := by
  classical
  by_cases hf : C.Closed (fun x=>(first.signature src.H x : AlgebraicComplex))
  · by_cases hg : C.Closed (fun x=>(second.signature src.H x : AlgebraicComplex))
    · exact NoIOrdinaryRaw.NoXGeneralEvenAntiBinary.countingHard G src
        (A.binary src.K src.H first second hf hg nonaffine nonproduct antiRow) antiRow v w hv hw anti
        (A.binary_nonaffine src.K src.H first second hf hg nonaffine nonproduct antiRow v w hv hw anti)
        (A.binary_nonproduct src.K src.H first second hf hg nonaffine nonproduct antiRow v w hv hw anti)
    · exact NoIOrdinaryRaw.NoXGeneralEvenAntiBinary.countingHard G src
        (N.binary src.K src.H second hg antiRow) antiRow v w hv hw anti
        (N.binary_nonaffine src.K src.H second hg antiRow v w hv hw anti)
        (N.binary_nonproduct src.K src.H second hg antiRow v w hv hw anti)
  · exact NoIOrdinaryRaw.NoXGeneralEvenAntiBinary.countingHard G src
      (N.binary src.K src.H first hf antiRow) antiRow v w hv hw anti
      (N.binary_nonaffine src.K src.H first hf antiRow v w hv hw anti)
      (N.binary_nonproduct src.K src.H first hf antiRow v w hv hw anti)

variable (negative : StableHigherCurrentOrdinaryTerminal.Obstruction (preprocess (NoIOrdinaryRaw.GenericOrdinarySource.family G src)))
include hv hw anti negative in
theorem hard_of_even (bad : B.EvenBad src.H) : NoIOrdinaryRaw.NoXWeightedAntiResourcesOriginal.Hard G := by
  obtain ⟨m,row,hbad⟩ := bad
  let second : B.Block (s:=src.size) (b:=src.b) (NoIOrdinaryRaw.NoXNonproduct.arity G src negative) :=
    ⟨0,NoIOrdinaryRaw.NoXNonproduct.blocks G src negative,NoIOrdinaryRaw.NoXNonproduct.balanced G src negative⟩
  exact countingHard G src row second antiRow v w hv hw anti hbad
    (NoIOrdinaryRaw.NoXNonproduct.row_nonproduct G src negative)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIOrdinaryRaw.NoXGeneralEvenAntiResources
end
