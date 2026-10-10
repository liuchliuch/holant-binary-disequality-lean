import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeXUniversalResource
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeSparseRankThreeOddSource
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeSparseRankThreeUniformOddSource

/-! Rank-three suppliers with no resource or class backend as a hypothesis.
All maps, row multiplicities, signs, private bits, original labels, coefficient
values, and residual classes are constructed from the actual minimal witness. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeXRankThreeSupplier
open Holant Holant.Tractable Holant.Algebraic
open OrdinaryNegativeSignedPortsCore
namespace P
export OrdinaryNegativeSparseMinimalRank (PinWitness row)
export OrdinaryNegativeSparseUniformMinimal (UniformPinWitness)
end P
namespace A
export OrdinaryNegativeSparseRankThreeActualSource (choose block block_nonaffine)
end A
namespace U
export OrdinaryNegativeSparseRankThreeUniformSource (choose block block_nonaffine)
export OrdinaryNegativeAffineRankOne (uniform)
end U
namespace O
export OrdinaryNegativeSparseRankThreeOddSource
  (recipe signature value constant_even boundary_odd private_even alpha)
end O
namespace V
export OrdinaryNegativeSparseRankThreeUniformOddSource
  (recipe signature value constant_even boundary_odd private_even affine)
end V
namespace R
export OrdinaryNegativeSparseRankThreePorts (port word_code)
export OrdinaryNegativeSignedPortsIncidence (bundleSize)
end R
namespace X
export OrdinaryNegativeXUniversalResource (EvenBad AlphaResource AffineResource)
end X
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 32768
set_option Elab.async false

variable {K : IntermediateField ℚ AlgebraicComplex} {N : ℕ} {f : Signature K N}
local instance : Algebra ℚ K := K.algebra'
variable {s : ℕ} {b : ℕ→ℕ}
variable (H : (j : Fin s)→Signature K (b j.val)) (labels : Fin 4→Fin s)
variable (literal : ∀i,(⟨b (labels i).val,H (labels i)⟩ : AnySignature K)=⟨arity N i.val,table f i⟩)
variable (square : Affine (fun x=>(f x : AlgebraicComplex)^2))

section Identity
variable (W : P.PinWitness f 3)
variable (minimal : ∀S : Finset (Fin 3),S.card<3→∀z : Fin 3→Bool,
  Affine (OrdinaryNegativeSparseRankDescent.minor W.chart S z))
variable (odd : ∀j,Odd (R.bundleSize (R.port W.chart) j))

def alphaResource : X.AlphaResource H .seven where
  privateCount := N
  rows := O.recipe W H labels literal
  constant_even := O.constant_even W H labels literal
  boundary_odd := O.boundary_odd W H labels literal odd
  private_even := O.private_even W H labels literal
  alpha := O.alpha W H labels literal odd square minimal
  full := by
    intro x
    change (O.signature W H labels literal (OrdinaryNegativeSparseMixingAlpha.codeSeven x) : AlgebraicComplex)≠0
    rw [O.value]
    change P.row f W.pins (word (R.port W.chart) (OrdinaryNegativeSparseMixingAlpha.codeSeven x))≠0
    rw [R.word_code]
    exact W.chart.supported x

include literal square minimal in
theorem identity : X.EvenBad H ∨ Nonempty (X.AlphaResource H .seven) := by
  rcases A.choose W minimal square with odd|hd
  · exact Or.inr ⟨alphaResource H labels literal square W minimal odd⟩
  · let D := Classical.choice hd
    exact Or.inl ⟨7,A.block W H labels literal D,A.block_nonaffine W H labels literal D⟩
end Identity

section Uniform
variable (W : P.UniformPinWitness f 3)
variable (minimal : ∀S : Finset (Fin 3),S.card<3→∀z : Fin 3→Bool,
  Affine (U.uniform (OrdinaryNegativeSparseRankDescent.minor W.chart S z)))
variable (odd : ∀j,Odd (R.bundleSize (R.port W.chart) j))

def affineResource : X.AffineResource H .seven where
  privateCount := N
  rows := V.recipe W H labels literal
  constant_even := V.constant_even W H labels literal
  boundary_odd := V.boundary_odd W H labels literal odd
  private_even := V.private_even W H labels literal
  affine := V.affine W H labels literal odd square minimal
  full := by
    intro x
    change (V.signature W H labels literal (OrdinaryNegativeSparseMixingAlpha.codeSeven x) : AlgebraicComplex)≠0
    rw [V.value]
    change P.row f W.pins (word (R.port W.chart) (OrdinaryNegativeSparseMixingAlpha.codeSeven x))≠0
    rw [R.word_code]
    exact W.chart.supported x

include literal square minimal in
theorem uniform : X.EvenBad H ∨ Nonempty (X.AffineResource H .seven) := by
  rcases U.choose W minimal square with odd|hd
  · exact Or.inr ⟨affineResource H labels literal square W minimal odd⟩
  · let D := Classical.choice hd
    exact Or.inl ⟨7,U.block W H labels literal D,U.block_nonaffine W H labels literal D⟩
end Uniform

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeXRankThreeSupplier
end
