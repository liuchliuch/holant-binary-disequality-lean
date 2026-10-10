import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoXOrdinaryGraphSource
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoXReciprocalSelectionSquares
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoIOrdinaryEvenHardness
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeCubicGadgets
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.GenericOrdinarySource
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoXWeightedAntiResourcesOriginal
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.Target

/-! Quantification over actual ordinary graphs retains one fixed original
oracle. In the absence of its genuine counting hardness, every graph row has
an Affine square; this supplies support geometry for physical rank descent. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIOrdinaryRaw.NoIOrdinarySelectionClosure
open Holant Holant.Tractable
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace M
export OrdinaryNegativeCubicGadgets (Macro)
end M
namespace E
export NoIOrdinaryRaw.GenericOrdinarySource (field count arity table family)
end E
namespace X
export NoIOrdinaryRaw.NoXOrdinaryGraphSource (data old_literal new_literal old_included)
end X
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : NoIOrdinaryRaw.Target)
variable (src : NoIOrdinaryRaw.GenericOrdinarySource.Data G)
local instance : Algebra ℚ src.K := src.K.algebra'
variable {n : ℕ} (N : M.Macro src.H n)

def output : NoXOrdinaryGraphAdjoin.Output src.H n :=
  ⟨N.network,N.labels,N.exact,N.edges⟩

def extension : NoIOrdinaryRaw.GenericOrdinarySource.Data G := X.data G src (output G src N)

theorem included : E.family G src⊆E.family G (extension G src N) :=
  X.old_included G src (output G src N)

variable (negative : StableHigherCurrentOrdinaryTerminal.Obstruction (preprocess (E.family G src)))
include negative in
theorem obstruction : StableHigherCurrentOrdinaryTerminal.Obstruction
    (preprocess (E.family G (extension G src N))) := by
  apply (NoIOrdinaryRaw.GenericOrdinarySource.rejected_iff G (extension G src N)).mp
  intro tract
  exact ((NoIOrdinaryRaw.GenericOrdinarySource.rejected_iff G src).mpr negative)
    (tract.mono_family (included G src N))


include negative in
theorem square (noHard : ¬NoIOrdinaryRaw.NoXWeightedAntiResourcesOriginal.Hard G) :
    Affine (fun x=>(N.network.denote x : AlgebraicComplex)^2) := by
  have squares := NoIOrdinaryRaw.NoXReciprocalSelectionSquares.evenBad_or_squares G (extension G src N)
  have noBad : ¬OrdinaryNegativeXUniversalResource.EvenBad (extension G src N).H := by
    intro bad
    apply noHard
    apply NoIOrdinaryRaw.NoIOrdinaryEvenHardness.countingHard G (extension G src N)
      (obstruction G src N negative) bad
  have squares := squares.resolve_left noBad
  have h : (⟨(extension G src N).b (NoXOrdinaryGraphAdjoin.newLabel src.H).val,
      (extension G src N).H (NoXOrdinaryGraphAdjoin.newLabel src.H)⟩ : AnySignature src.K)∈
      {f : AnySignature src.K | Affine (fun x=>(f.2 x : AlgebraicComplex)^2)} :=
    squares (NoXOrdinaryGraphAdjoin.newLabel src.H)
  change (⟨(X.data G src (output G src N)).b (NoXOrdinaryGraphAdjoin.newLabel src.H).val,
      (X.data G src (output G src N)).H (NoXOrdinaryGraphAdjoin.newLabel src.H)⟩ : AnySignature src.K)∈
      {f : AnySignature src.K | Affine (fun x=>(f.2 x : AlgebraicComplex)^2)} at h
  rw [X.new_literal G src (output G src N)] at h
  exact h

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIOrdinaryRaw.NoIOrdinarySelectionClosure
end
