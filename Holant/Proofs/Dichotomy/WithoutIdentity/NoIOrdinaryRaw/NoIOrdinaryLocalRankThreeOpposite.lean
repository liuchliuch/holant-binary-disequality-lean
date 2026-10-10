import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralLocalRankThreeBundle
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralRankThreePinPorts
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralRankThreeTotalOddPhase
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalRankThreeSchedule
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalRankThreeLocal
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoIOrdinaryLocalRankTwoOpposite
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.GenericOrdinarySource
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoIOrdinaryEvenHardness
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoIOrdinaryLocalRankTwoFaces
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoIOrdinarySelectionClosure
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoXGeneralLocalMasks
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoXOrdinaryGraphSource
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoXWeightedAntiResourcesOriginal
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.Target

/-! Least-LocalAffine rank three supplies an actual Affine opposite-simplex
resource on fourteen ports. The parity repairs use supported L correction
twists; total-odd is excluded by parallel faces; separately-odd leaves all
proper physical faces Affine and forces the remaining row Affine. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIOrdinaryRaw.NoIOrdinaryLocalRankThreeOpposite
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open OrdinaryNegativeAffineSystematicSupport OrdinaryNegativeSparseRankDescent
namespace M
export OrdinaryNegativeCubicGadgets (Macro)
end M
namespace Q
export OrdinaryNegativeSparseRankThreePorts (port word_code)
export OrdinaryNegativeSparseMixingAlpha (codeSeven)
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

theorem pin_square {n : ℕ} (f : Signature AlgebraicComplex n) (square : Affine (fun x=>f x^2))
    (p : Fin n) (bit : Bool) : Affine (fun x=>pinMask f p bit x^2):=by
  have actual:=square.restrict (system (Finset.univ.erase p) (fun _=>bit))
  have holds (x : Word n) : (system (Finset.univ.erase p) (fun _=>bit)).Holds x ↔ x p=bit:=by
    rw [system_holds]
    simp
  convert actual using 1
  funext x
  by_cases hx : x p=bit <;> simp [pinMask,holds,hx]

variable {s : ℕ} {a : ℕ→ℕ}
variable (G : NoIOrdinaryRaw.Target)
variable (src : NoIOrdinaryRaw.GenericOrdinarySource.Data G)
local instance : Algebra ℚ src.K:=src.K.algebra'
variable (negative : StableHigherCurrentOrdinaryTerminal.Obstruction (preprocess (NoIOrdinaryRaw.GenericOrdinarySource.family G src)))

include negative in
theorem label (noHard : ¬NoIOrdinaryRaw.NoXWeightedAntiResourcesOriginal.Hard G) (j : Fin src.size)
    (D : SystematicSupport (fun x=>(src.H j x : AlgebraicComplex)) 3)
    (square : Affine (fun x=>(src.H j x : AlgebraicComplex)^2))
    (bad : ¬LocalAffine (fun x=>(src.H j x : AlgebraicComplex)))
    (masks : ∀i bit,LocalAffine (pinMask (fun x=>(src.H j x : AlgebraicComplex)) (D.ports i) bit)) :
    ∃T : R.OddResource (s:=src.size) src.b 14,Affine (T.ambient src.H) ∧
      ∀x : Word 3,T.ambient src.H (R.embedding .seven x)≠0 := by
  have odd : ∀q bit,Odd (Q.signedCount (Q.port D) q bit):=by
    rcases NoXReciprocalRankThreeSchedule.choose (Q.port D) with total|both|⟨k,schedule,even⟩
    · exact False.elim (NoXGeneralRankThreeTotalOddPhase.incompatible D square (masks 0) (total 6))
    · exact both
    · have nonaffine:=NoXGeneralLocalRankThreeBundle.nonaffine D schedule masks square bad even
      exact False.elim (noHard (NoIOrdinaryRaw.NoIOrdinaryEvenHardness.countingHard G src negative
        (NoXGeneralSeparateRows.evenBad src.H j (src.p false) (src.p true) (src.hp false) (src.hp true)
          (NoXGeneralLocalRankThreeBundle.rows D schedule) even nonaffine)))
  have affineMasks (i : Fin 3) (bit : Bool) :
      Affine (pinMask (fun x=>(src.H j x : AlgebraicComplex)) (D.ports i) bit):=
    NoXGeneralRankThreePinPorts.affine_mask D odd i bit (pin_square _ square _ _) (masks i bit)
  have faces : ∀S : Finset (Fin 3),S.card<3→∀z : Word 3,Affine (minor D S z):=by
    intro S smaller z
    have outside : ∃i : Fin 3,i∉S:=by
      by_contra h
      push Not at h
      have all : S=Finset.univ:=Finset.eq_univ_of_forall h
      simp [all] at smaller
    obtain ⟨i,hi⟩:=outside
    exact NoIOrdinaryRaw.NoIOrdinaryLocalRankTwoFaces.minor_of_mask D S z i hi (affineMasks i (z i))
  have good : Affine (fun x=>(src.H j x : AlgebraicComplex)):=by
    by_contra failure
    exact bad (NoXReciprocalRankThreeLocal.local_affine _ D (Q.port D) (Q.word_code D) odd square failure faces)
  let T:=NoXSeparateSignedSource.resource src.H j (src.p false) (src.p true)
    (src.hp false) (src.hp true) (Q.port D) odd
  refine ⟨T,NoXGeneralSeparateAffineSource.affine src.H j (src.p false) (src.p true)
    (src.hp false) (src.hp true) (Q.port D) odd good,?_⟩
  intro x
  change T.ambient src.H (Fin.addCases (Q.codeSeven x) (fun i=> !(Q.codeSeven x i)))≠0
  rw [NoXSeparateSignedSource.ambient_value,Q.word_code]
  exact D.supported x

include negative in
theorem graph {n : ℕ} (noHard : ¬NoIOrdinaryRaw.NoXWeightedAntiResourcesOriginal.Hard G) (N : M.Macro src.H (n+2))
    (D : SystematicSupport (fun x=>(N.network.denote x : AlgebraicComplex)) 3)
    (bad : ¬LocalAffine (fun x=>(N.network.denote x : AlgebraicComplex)))
    (minimal : ¬NoXGeneralLocalMinimalGraph.Witness (n:=n) (H:=src.H) src.K.subtype 2) :
    ∃T : R.OddResource (s:=(C.extension G src N).size) (C.extension G src N).b 14,
      Affine (T.ambient (C.extension G src N).H) ∧
      ∀x : Word 3,T.ambient (C.extension G src N).H (R.embedding .seven x)≠0 := by
  let dst:=C.extension G src N
  let j:=NoXOrdinaryGraphAdjoin.newLabel src.H
  let property (f : AnySignature src.K) : Prop:=
    ∀D : SystematicSupport (fun x=>(f.2 x : AlgebraicComplex)) 3,
      Affine (fun x=>(f.2 x : AlgebraicComplex)^2)→
      ¬LocalAffine (fun x=>(f.2 x : AlgebraicComplex))→
      (∀i bit,LocalAffine (pinMask (fun x=>(f.2 x : AlgebraicComplex)) (D.ports i) bit))→
      ∃T : R.OddResource (s:=dst.size) dst.b 14,Affine (T.ambient dst.H) ∧
        ∀x : Word 3,T.ambient dst.H (R.embedding .seven x)≠0
  have consume : property ⟨dst.b j.val,dst.H j⟩:=by
    intro chart sq failure masks
    exact label G dst (C.obstruction G src N negative) noHard j chart sq failure masks
  have lit : (⟨dst.b j.val,dst.H j⟩ : AnySignature src.K)=⟨n+2,N.network.denote⟩:=
    NoIOrdinaryRaw.NoXOrdinaryGraphSource.new_literal G src (C.output G src N)
  rw [lit] at consume
  exact consume D (C.square G src N negative noHard) bad
    (NoIOrdinaryRaw.NoXGeneralLocalMasks.local_masks G src N D minimal)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIOrdinaryRaw.NoIOrdinaryLocalRankThreeOpposite
end
