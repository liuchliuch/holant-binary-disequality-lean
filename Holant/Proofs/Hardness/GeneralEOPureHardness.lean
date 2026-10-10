import Holant.Proofs.Hardness.GeneralEOPureLoopSource
import Holant.Proofs.Hardness.GeneralEOPureClosedFamily
import Holant.Proofs.Hardness.GeneralEOCommonSignSelection

/-! Original-family hardness for the pure common-sign lane. The literal EO
criterion supplies two bad ordered pairings; native forced-coordinate loops
produce the closed macros internally. No auxiliary signature, pairing cover,
class failure of a supplied gadget, or hardness backend is a caller premise. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPureHardness
open Computability Holant Holant.Tractable Holant.Complexity Holant.Algebraic
open FixedGadgetSubstitution
namespace R
export GeneralEOPureLoopCore (Reduced)
end R
namespace O
export Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalTarget
  (originalPresentation originalValue)
end O
namespace Standard
export Holant.LocalDrafts.MainChain.CBStandardNativeHardness.Standard
  (Model injectedEncoding standard_to_witness)
end Standard
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
set_option Elab.async false
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
variable (sign : EOSign)
variable (he : ∀i,Signature.CentralSupport (G i))
variable (hs : ∀i,EONegativeWitness.Supports sign ⟨a i.val,G i⟩)
variable (hp : ∀i,GeneralEODEQProducerSupportBasic.Pure sign (G i))
variable (negative : ¬EOTract (preprocess (EONegativePairReduction.family G)))

include he hs hp negative in
theorem reduced_exists (C : EOClass) : Nonempty (R.Reduced G C) := by
  obtain ⟨j,_hj,p,hbad⟩ := GeneralEOCommonSignSelection.class_failure G sign he hs negative C
  refine GeneralEOPureLoopSource.reduce G sign C (a j.val) (Network.corolla (G j))
    (LabelledNetwork.corolla G j) (LabelledNetwork.exact_corolla G j)
    (fun e => Fin.elim0 e) ?_ ?_ ?_ p ?_
  · simpa only [Network.denote_corolla] using he j
  · simpa only [Network.denote_corolla] using hs j
  · simpa only [Network.denote_corolla] using hp j
  · simpa only [Network.denote_corolla] using hbad

def reduced (C : EOClass) : R.Reduced G C :=
  Classical.choice (reduced_exists G sign he hs hp negative C)

attribute [local irreducible] GeneralEOPureClosedFamily.source
variable {α : Type} {ea : Encoding α Bool} {count : α → ℕ}

/-- Actual controlled source for every natural-number #P witness, ending at
originalValue G and the original ordered-label and algebraic answer codecs. -/
def source (w : SharpPWitness ea count) : LengthControlledOracleReduction ea encodingNatBool
    (RawClosedNetwork.validatedEncoding s 1 a) (O.originalPresentation G).encoding
    count (O.originalValue G) :=
  GeneralEOPureClosedFamily.source G (reduced G sign he hs hp negative .affine)
    (reduced G sign he hs hp negative .product) w

include he hs hp negative in
theorem witnessCountingHard : Holant.LocalDrafts.CountingHardness.WitnessCountingHard
    (RawClosedNetwork.validatedEncoding s 1 a) (O.originalPresentation G).encoding
    (O.originalValue G) := by
  intro α ea f w
  exact ⟨(source G sign he hs hp negative w).reduction⟩

variable {Δ Q : Type} [Fintype Δ] [Fintype Q]
variable (m : Standard.Model Δ Q) (input : Bool → Δ) (hinj : Function.Injective input)
variable (clock : Polynomial ℕ) (htime : m.PolyTimeOn input clock)

def standardSource : LengthControlledOracleReduction ea encodingNatBool
    (RawClosedNetwork.validatedEncoding s 1 a) (O.originalPresentation G).encoding
    (m.physicalCount (Standard.injectedEncoding ea input hinj)) (O.originalValue G) :=
  source G sign he hs hp negative (Standard.standard_to_witness (ea:=ea) m input hinj clock htime)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPureHardness
