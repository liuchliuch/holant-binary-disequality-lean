import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeRankTwoUniformOddSource
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeXUniversalResource

/-! Original-label rank-two alternatives for universal X assembly. Recipe
selection, parity correction and complementary class membership are proved
upstream from actual minimal pin witnesses, with no canonical row oracle. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeRankTwoUniversalSupply
open Holant Holant.Tractable Holant.Algebraic
open OrdinaryNegativeSignedPortsCore OrdinaryNegativeSparseRankDescent
namespace P
export OrdinaryNegativeSparseMinimalRank (PinWitness)
export OrdinaryNegativeSparseUniformMinimal (UniformPinWitness)
end P
namespace A
export OrdinaryNegativeRankTwoActualSource (choose block block_nonaffine)
end A
namespace U
export OrdinaryNegativeRankTwoUniformSource (choose block block_nonaffine)
end U
namespace O
export OrdinaryNegativeRankTwoOddSource (recipe signature alpha support_exact constant_even boundary_odd private_even)
end O
namespace V
export OrdinaryNegativeRankTwoUniformOddSource (recipe signature affine support_exact constant_even boundary_odd private_even)
end V
namespace R
export OrdinaryNegativeXUniversalResource (AlphaResource AffineResource EvenBad)
end R
namespace Q
export OrdinaryNegativeRankTwoPorts (port)
export OrdinaryNegativeSignedPortsIncidence (bundleSize)
end Q
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
variable {K : IntermediateField ℚ AlgebraicComplex} {N : ℕ} {f : Signature K N}
local instance : Algebra ℚ K := K.algebra'
variable {s : ℕ} {b : ℕ→ℕ}
variable (H : (j : Fin s)→Signature K (b j.val)) (labels : Fin 4→Fin s)
variable (literal : ∀i,(⟨b (labels i).val,H (labels i)⟩ : AnySignature K)=⟨arity N i.val,table f i⟩)
variable (square : Affine (fun x=>(f x : AlgebraicComplex)^2))

def alphaResource (W : P.PinWitness f 2)
    (odd : ∀j,Odd (Q.bundleSize (Q.port W.chart) j))
    (minimal : ∀S : Finset (Fin 2),S.card<2→∀z : Fin 2→Bool,Affine (minor W.chart S z)) :
    R.AlphaResource H .three where
  privateCount := N
  rows := O.recipe W H labels literal
  constant_even := O.constant_even W H labels literal
  boundary_odd := O.boundary_odd W H labels literal odd
  private_even := O.private_even W H labels literal
  alpha := O.alpha W H labels literal odd square minimal
  full := by
    intro x
    change (O.signature W H labels literal (OrdinaryNegativeSparseMixingAlpha.codeThree x) : AlgebraicComplex)≠0
    rw [O.support_exact W H labels literal odd]
    rfl

def affineResource (W : P.UniformPinWitness f 2)
    (odd : ∀j,Odd (Q.bundleSize (Q.port W.chart) j))
    (minimal : ∀S : Finset (Fin 2),S.card<2→∀z : Fin 2→Bool,
      Affine (OrdinaryNegativeAffineRankOne.uniform (minor W.chart S z))) : R.AffineResource H .three where
  privateCount := N
  rows := V.recipe W H labels literal
  constant_even := V.constant_even W H labels literal
  boundary_odd := V.boundary_odd W H labels literal odd
  private_even := V.private_even W H labels literal
  affine := V.affine W H labels literal odd square minimal
  full := by
    intro x
    change (V.signature W H labels literal (OrdinaryNegativeSparseMixingAlpha.codeThree x) : AlgebraicComplex)≠0
    rw [V.support_exact W H labels literal odd]
    rfl

include square literal in
theorem ordinary (W : P.PinWitness f 2)
    (minimal : ∀S : Finset (Fin 2),S.card<2→∀z : Fin 2→Bool,Affine (minor W.chart S z)) :
    R.EvenBad H ∨ Nonempty (R.AlphaResource H .three) := by
  rcases A.choose W (square:=square) (minimal:=minimal) with odd|data
  · exact Or.inr ⟨alphaResource H labels literal square W odd minimal⟩
  · obtain ⟨D⟩ := data
    exact Or.inl ⟨3,A.block W H labels literal D,A.block_nonaffine W H labels literal D⟩

include square literal in
theorem uniform (W : P.UniformPinWitness f 2)
    (minimal : ∀S : Finset (Fin 2),S.card<2→∀z : Fin 2→Bool,
      Affine (OrdinaryNegativeAffineRankOne.uniform (minor W.chart S z))) :
    R.EvenBad H ∨ Nonempty (R.AffineResource H .three) := by
  rcases U.choose W (square:=square) (minimal:=minimal) with odd|data
  · exact Or.inr ⟨affineResource H labels literal square W odd minimal⟩
  · obtain ⟨D⟩ := data
    exact Or.inl ⟨3,U.block W H labels literal D,U.block_nonaffine W H labels literal D⟩

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeRankTwoUniversalSupply
end
