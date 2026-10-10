import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXOrdinaryGraphSource
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalSelectionSquares
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralEvenHardness
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeCubicGadgets

/-! Quantification over actual ordinary graphs retains one fixed original
oracle. In the absence of its genuine counting hardness, every graph row has
an Affine square; this supplies support geometry for physical rank descent. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalSelectionClosure
open Holant Holant.Tractable
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace M
export OrdinaryNegativeCubicGadgets (Macro)
end M
namespace E
export GenericOrdinarySource (field count arity table family)
end E
namespace X
export NoXOrdinaryGraphSource (data old_literal new_literal old_included)
end X
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (src : GenericOrdinarySource.Data G)
local instance : Algebra ℚ src.K := src.K.algebra'
variable {n : ℕ} (N : M.Macro src.H n)

def output : NoXOrdinaryGraphAdjoin.Output src.H n :=
  ⟨N.network,N.labels,N.exact,N.edges⟩

def extension : GenericOrdinarySource.Data G := X.data G src (output G src N)

theorem included : E.family G src⊆E.family G (extension G src N) :=
  X.old_included G src (output G src N)

variable (negative : StableHigherCurrentOrdinaryTerminal.Obstruction (preprocess (E.family G src)))
include negative in
theorem obstruction : StableHigherCurrentOrdinaryTerminal.Obstruction
    (preprocess (E.family G (extension G src N))) := by
  apply (GenericOrdinarySource.rejected_iff G (extension G src N)).mp
  intro tract
  exact ((GenericOrdinarySource.rejected_iff G src).mpr negative)
    (tract.mono_family (included G src N))

variable (zLabel : Fin src.size)
variable (literal : (⟨src.b zLabel.val,src.H zLabel⟩ : AnySignature src.K)=
  ⟨2,NoXGeneralZSign.signature⟩)

include negative literal in
theorem square (noHard : ¬NoXWeightedAntiResourcesOriginal.Hard G) :
    Affine (fun x=>(N.network.denote x : AlgebraicComplex)^2) := by
  have squares := NoXReciprocalSelectionSquares.evenBad_or_squares G (extension G src N)
  have noBad : ¬OrdinaryNegativeXUniversalResource.EvenBad (extension G src N).H := by
    intro bad
    apply noHard
    apply NoXGeneralEvenHardness.countingHard G (extension G src N)
      (NoXOrdinaryGraphAdjoin.old src.H zLabel)
      ((X.old_literal G src (output G src N) zLabel).trans literal)
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

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalSelectionClosure
end
