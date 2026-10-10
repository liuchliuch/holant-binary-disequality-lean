import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoIOrdinaryLocalRankTwoCounts
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralSeparateEvenLocal
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralSeparateAffineSource
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralRankTwoLocal
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeRankTwoAlphaCore
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.GenericOrdinarySource
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoIOrdinaryEvenHardness
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoIOrdinaryLocalRankTwoFaces
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoIOrdinarySelectionClosure
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoXOrdinaryGraphSource
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoXWeightedAntiResourcesOriginal
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.Target

/-! Genuine least-LocalAffine rank two yields an actual Affine six-port
odd-boundary resource, full on the opposite simplex code. The graph is
installed once into the source, preserving its original counting oracle. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIOrdinaryRaw.NoIOrdinaryLocalRankTwoOpposite
open Holant Holant.Tractable
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open OrdinaryNegativeAffineSystematicSupport OrdinaryNegativeSparseRankDescent
namespace M
export OrdinaryNegativeCubicGadgets (Macro)
end M
namespace Q
export OrdinaryNegativeRankTwoPorts (port word_code essential_nonaffine)
export OrdinaryNegativeSparseMixingAlpha (codeThree codeThree_affine)
export NoXSeparateSignedProjection (signedCount)
end Q
namespace C
export NoIOrdinaryRaw.NoIOrdinarySelectionClosure (output extension obstruction square)
end C
namespace R
export OrdinaryNegativeXUniversalResource (OddResource)
export NoXWeightedAntiOppositeCap (embedding)
end R
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : NoIOrdinaryRaw.Target)
variable (src : NoIOrdinaryRaw.GenericOrdinarySource.Data G)
local instance : Algebra ℚ src.K:=src.K.algebra'
variable (negative : StableHigherCurrentOrdinaryTerminal.Obstruction (preprocess (NoIOrdinaryRaw.GenericOrdinarySource.family G src)))

include negative in
theorem label (noHard : ¬NoIOrdinaryRaw.NoXWeightedAntiResourcesOriginal.Hard G) (j : Fin src.size)
    (D : SystematicSupport (fun x=>(src.H j x : AlgebraicComplex)) 2)
    (square : Affine (fun x=>(src.H j x : AlgebraicComplex)^2))
    (bad : ¬LocalAffine (fun x=>(src.H j x : AlgebraicComplex)))
    (parity : (∀q bit,Even (Q.signedCount (Q.port D) q bit)) ∨
      (∀q bit,Odd (Q.signedCount (Q.port D) q bit)))
    (faces : ∀S : Finset (Fin 2),S.card<2→∀z : Fin 2→Bool,Affine (minor D S z)) :
    ∃T : R.OddResource (s:=src.size) src.b 6,Affine (T.ambient src.H) ∧
      ∀x : Fin 2→Bool,T.ambient src.H (R.embedding .three x)≠0 := by
  have odd : ∀q bit,Odd (Q.signedCount (Q.port D) q bit):=by
    rcases parity with even|odd
    · have good : Affine (fun x=>(src.H j x : AlgebraicComplex)):=by
        by_contra failure
        have nonzero : (fun x=>(src.H j x : AlgebraicComplex))≠0:=by
          intro zero;exact D.supported (fun _=>false) (congrFun zero _)
        exact noHard (NoIOrdinaryRaw.NoIOrdinaryEvenHardness.countingHard G src negative
          (NoXReciprocalSelectionEvenProjection.evenBad src.H j (src.p false) (src.p true)
            (src.hp false) (src.hp true) (Q.port D) even
            (Q.essential_nonaffine D square nonzero failure)))
      exact False.elim (bad (NoXGeneralSeparateEvenLocal.local_of_affine (Q.port D) even D
        Q.codeThree Q.codeThree_affine (Q.word_code D) square good))
    · exact odd
  have good : Affine (fun x=>(src.H j x : AlgebraicComplex)):=by
    by_contra failure
    exact bad (NoXGeneralRankTwoLocal.local_affine _ D (Q.port D) (Q.word_code D) odd square failure
      (OrdinaryNegativeRankTwoAlphaCore.minimal_commonFourth D faces))
  let T:=NoXSeparateSignedSource.resource src.H j (src.p false) (src.p true)
    (src.hp false) (src.hp true) (Q.port D) odd
  refine ⟨T,NoXGeneralSeparateAffineSource.affine src.H j (src.p false) (src.p true)
    (src.hp false) (src.hp true) (Q.port D) odd good,?_⟩
  intro x
  change T.ambient src.H (Fin.addCases (Q.codeThree x) (fun i=> !(Q.codeThree x i)))≠0
  rw [NoXSeparateSignedSource.ambient_value,Q.word_code]
  exact D.supported x

include negative in
theorem graph {n : ℕ} (noHard : ¬NoIOrdinaryRaw.NoXWeightedAntiResourcesOriginal.Hard G) (N : M.Macro src.H (n+2))
    (D : SystematicSupport (fun x=>(N.network.denote x : AlgebraicComplex)) 2)
    (bad : ¬LocalAffine (fun x=>(N.network.denote x : AlgebraicComplex)))
    (minimal : ¬NoXGeneralLocalMinimalGraph.Witness (n:=n) (H:=src.H) src.K.subtype 1) :
    ∃T : R.OddResource (s:=(C.extension G src N).size) (C.extension G src N).b 6,
      Affine (T.ambient (C.extension G src N).H) ∧
      ∀x : Fin 2→Bool,T.ambient (C.extension G src N).H (R.embedding .three x)≠0 := by
  let dst:=C.extension G src N
  let j:=NoXOrdinaryGraphAdjoin.newLabel src.H
  let property (f : AnySignature src.K) : Prop:=
    ∀D : SystematicSupport (fun x=>(f.2 x : AlgebraicComplex)) 2,
      Affine (fun x=>(f.2 x : AlgebraicComplex)^2)→
      ¬LocalAffine (fun x=>(f.2 x : AlgebraicComplex))→
      ((∀q bit,Even (Q.signedCount (Q.port D) q bit)) ∨ (∀q bit,Odd (Q.signedCount (Q.port D) q bit)))→
      (∀S : Finset (Fin 2),S.card<2→∀z : Fin 2→Bool,Affine (minor D S z))→
      ∃T : R.OddResource (s:=dst.size) dst.b 6,Affine (T.ambient dst.H) ∧
        ∀x : Fin 2→Bool,T.ambient dst.H (R.embedding .three x)≠0
  have consume : property ⟨dst.b j.val,dst.H j⟩:=by
    intro chart sq failure parity faces
    exact label G dst (C.obstruction G src N negative) noHard j chart sq failure parity faces
  have lit : (⟨dst.b j.val,dst.H j⟩ : AnySignature src.K)=⟨n+2,N.network.denote⟩:=
    NoIOrdinaryRaw.NoXOrdinaryGraphSource.new_literal G src (C.output G src N)
  rw [lit] at consume
  exact consume D (C.square G src N negative noHard) bad
    (NoIOrdinaryRaw.NoIOrdinaryLocalRankTwoCounts.parity G src negative N D minimal noHard)
    (fun S hs z=>(NoIOrdinaryRaw.NoIOrdinaryLocalRankTwoFaces.faces G src negative N D minimal noHard S hs z).1)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIOrdinaryRaw.NoIOrdinaryLocalRankTwoOpposite
end
