import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoXOrdinaryGraphSource
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoXWeightedAntiSquares
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeCubicGadgets
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.GenericOrdinarySource
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoXWeightedAntiResourcesOriginal
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.Target

/-! Quantification over actual ordinary graphs retains one fixed original
oracle. In the absence of its genuine counting hardness, every graph row has
an Affine square; this supplies support geometry for physical rank descent. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIOrdinaryRaw.NoXOriginGraphClosure
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

variable (antiLabel : Fin src.size) (v w : src.K)
variable (hv : v≠0) (hw : w≠0)
variable (literal : (⟨src.b antiLabel.val,src.H antiLabel⟩ : AnySignature src.K)=
  ⟨2,NoXWeightedAntiSigned.anti v w⟩)

def antiLabel' : Fin (extension G src N).size := NoXOrdinaryGraphAdjoin.old src.H antiLabel

include literal in
theorem anti_literal :
    (⟨(extension G src N).b (antiLabel' G src N antiLabel).val,
      (extension G src N).H (antiLabel' G src N antiLabel)⟩ : AnySignature src.K)=
      ⟨2,NoXWeightedAntiSigned.anti v w⟩ :=
  (X.old_literal G src (output G src N) antiLabel).trans literal

include negative hv hw literal in
theorem square (noHard : ¬NoIOrdinaryRaw.NoXWeightedAntiResourcesOriginal.Hard G) :
    Affine (fun x=>(N.network.denote x : AlgebraicComplex)^2) := by
  have squares := (NoIOrdinaryRaw.NoXWeightedAntiSquares.all_squares_or_countingHard G (extension G src N)
    (obstruction G src N negative) (antiLabel' G src N antiLabel) v w hv hw
    (anti_literal G src N antiLabel v w literal)).resolve_right noHard
  have h : (⟨(extension G src N).b (NoXOrdinaryGraphAdjoin.newLabel src.H).val,
      (extension G src N).H (NoXOrdinaryGraphAdjoin.newLabel src.H)⟩ : AnySignature src.K)∈
      {f : AnySignature src.K | Affine (fun x=>(f.2 x : AlgebraicComplex)^2)} :=
    squares (NoXOrdinaryGraphAdjoin.newLabel src.H)
  change (⟨(X.data G src (output G src N)).b (NoXOrdinaryGraphAdjoin.newLabel src.H).val,
      (X.data G src (output G src N)).H (NoXOrdinaryGraphAdjoin.newLabel src.H)⟩ : AnySignature src.K)∈
      {f : AnySignature src.K | Affine (fun x=>(f.2 x : AlgebraicComplex)^2)} at h
  rw [X.new_literal G src (output G src N)] at h
  exact h

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIOrdinaryRaw.NoXOriginGraphClosure
end
