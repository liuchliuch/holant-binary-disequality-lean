import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralRankTwoRegularSupply
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralRankTwoUniformRegularSupply
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralRankTwoMixedSource
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralRankTwoUniformMixedSource
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoXGeneralOddTernaryAnti
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.GenericOrdinarySource
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoXWeightedAntiResourcesOriginal
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.Target

/-! Complete pin-only rank-two parity selection over an ordinary source.
All repaired patterns yield actual EvenBad; noncanonical ternary shifts
produce original hardness; canonical shifts provide the A/alpha resource.
The genuine separately odd six-port residual is retained explicitly. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIOrdinaryRaw.NoXGeneralRankTwoSupply
open Holant Holant.Tractable
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open OrdinaryNegativeSparseRankDescent
namespace P
export OrdinaryNegativeSparseMinimalRank (PinWitness row)
export OrdinaryNegativeSparseUniformMinimal (UniformPinWitness)
export NoXSeparateSignedProjection (signedCount)
export OrdinaryNegativeSignedPortsIncidence (bundleSize)
end P
namespace Q
export OrdinaryNegativeRankTwoPorts (port)
end Q
namespace R
export OrdinaryNegativeXUniversalResource (EvenBad AlphaResource AffineResource)
export NoIOrdinaryRaw.NoXWeightedAntiResourcesOriginal (Hard)
end R
namespace O
export NoXGeneralMixedOrientation (sign)
end O
namespace A
export NoXGeneralRankTwoMixedSource (resource support_iff alphaResource)
end A
namespace U
export NoXGeneralRankTwoUniformMixedSource (resource support_iff affineResource)
export OrdinaryNegativeAffineRankOne (uniform)
end U
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 32768
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : NoIOrdinaryRaw.Target)
variable (src : NoIOrdinaryRaw.GenericOrdinarySource.Data G)
local instance : Algebra ℚ src.K := src.K.algebra'
variable (j : Fin src.size)
variable (square : Affine (fun x=>(src.H j x : AlgebraicComplex)^2))
variable (negative : StableHigherCurrentOrdinaryTerminal.Obstruction (preprocess (NoIOrdinaryRaw.GenericOrdinarySource.family G src)))

include square negative in
theorem total_ordinary (W : P.PinWitness (src.H j) 2)
    (minimal : ∀S : Finset (Fin 2),S.card<2→∀z : Fin 2→Bool,Affine (minor W.chart S z))
    (total : ∀q,Odd (P.bundleSize (Q.port W.chart) q)) :
    R.Hard G ∨ Nonempty (R.AlphaResource src.H .three) := by
  by_cases canonical : O.sign (Q.port W.chart) 2=(O.sign (Q.port W.chart) 0 ^^ O.sign (Q.port W.chart) 1)
  · right
    exact ⟨A.alphaResource src.H j (src.p false) (src.p true) (src.hp false) (src.hp true)
      W total square minimal canonical⟩
  · left
    exact NoIOrdinaryRaw.NoXGeneralOddTernaryAnti.countingHard G src
      (A.resource src.H j (src.p false) (src.p true) (src.hp false) (src.hp true) W total)
      (O.sign (Q.port W.chart))
      (A.support_iff src.H j (src.p false) (src.p true) (src.hp false) (src.hp true) W total)
      canonical negative

include square negative in
theorem total_uniform (W : P.UniformPinWitness (src.H j) 2)
    (minimal : ∀S : Finset (Fin 2),S.card<2→∀z : Fin 2→Bool,Affine (U.uniform (minor W.chart S z)))
    (total : ∀q,Odd (P.bundleSize (Q.port W.chart) q)) :
    R.Hard G ∨ Nonempty (R.AffineResource src.H .three) := by
  by_cases canonical : O.sign (Q.port W.chart) 2=(O.sign (Q.port W.chart) 0 ^^ O.sign (Q.port W.chart) 1)
  · right
    exact ⟨U.affineResource src.H j (src.p false) (src.p true) (src.hp false) (src.hp true)
      W total square minimal canonical⟩
  · left
    exact NoIOrdinaryRaw.NoXGeneralOddTernaryAnti.countingHard G src
      (U.resource src.H j (src.p false) (src.p true) (src.hp false) (src.hp true) W total)
      (O.sign (Q.port W.chart))
      (U.support_iff src.H j (src.p false) (src.p true) (src.hp false) (src.hp true) W total)
      canonical negative

include square negative in
theorem ordinary (W : P.PinWitness (src.H j) 2)
    (minimal : ∀S : Finset (Fin 2),S.card<2→∀z : Fin 2→Bool,Affine (minor W.chart S z)) :
    R.Hard G ∨ R.EvenBad src.H ∨ Nonempty (R.AlphaResource src.H .three) ∨
      ((∀q bit,Odd (P.signedCount (Q.port W.chart) q bit)) ∧ LocalAffine (P.row (src.H j) W.pins)) := by
  rcases NoXGeneralRankTwoRegularSupply.ordinary src.H j (src.p false) (src.p true)
    (src.hp false) (src.hp true) W square minimal with even|total|both
  · exact Or.inr (Or.inl even)
  · rcases total_ordinary G src j square negative W minimal total with hard|alpha
    · exact Or.inl hard
    · exact Or.inr (Or.inr (Or.inl alpha))
  · exact Or.inr (Or.inr (Or.inr ⟨both,NoXGeneralRankTwoRegularSupply.local_of_both src.H j W square minimal both⟩))

include square negative in
theorem uniform (W : P.UniformPinWitness (src.H j) 2)
    (minimal : ∀S : Finset (Fin 2),S.card<2→∀z : Fin 2→Bool,Affine (U.uniform (minor W.chart S z))) :
    R.Hard G ∨ R.EvenBad src.H ∨ Nonempty (R.AffineResource src.H .three) ∨
      (∀q bit,Odd (P.signedCount (Q.port W.chart) q bit)) := by
  rcases NoXGeneralRankTwoUniformRegularSupply.uniform src.H j (src.p false) (src.p true)
    (src.hp false) (src.hp true) W square minimal with even|total|both
  · exact Or.inr (Or.inl even)
  · rcases total_uniform G src j square negative W minimal total with hard|affine
    · exact Or.inl hard
    · exact Or.inr (Or.inr (Or.inl affine))
  · exact Or.inr (Or.inr (Or.inr both))


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIOrdinaryRaw.NoXGeneralRankTwoSupply
end
