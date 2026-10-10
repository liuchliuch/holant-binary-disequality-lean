import Holant.Proofs.Hardness.GeneralEOARSNonclosedSource
import Holant.Proofs.Hardness.GeneralEOPhaseControlledNonpureSource
import Holant.Proofs.Hardness.GeneralEOPureHardness
import Holant.Proofs.Hardness.GeneralEOPhaseSupportSource

/-! Universal finite-family negative EO source. The literal preprocessed
criterion and centrality of the original rows suffice. Common signs split
into the pure and nonpure sources. Without a common sign, pin elimination
consumes an actual support obstruction; the genuine ARS alternative has
nonclosed support and uses the unpinned ARS source. Zero and nullary rows
remain in the original dictionary, field, and answer codec throughout. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOUniversalSource
open Computability Holant Holant.Tractable Holant.Complexity
namespace C
export GeneralEOPhaseExtractionControlledSource (ControlledCountingHard)
end C
namespace O
export Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalTarget
  (originalField originalPresentation originalValue)
end O
namespace R
export EONegativePairReduction (family signature)
end R
namespace Standard
export Holant.LocalDrafts.MainChain.CBStandardNativeHardness.Standard
  (Model injectedEncoding standard_to_witness)
end Standard
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
variable (he : ∀i,Signature.CentralSupport (G i))
variable (negative : ¬EOTract (preprocess (R.family G)))

include he negative in
/-- A common support sign needs neither nonzero rows nor a supplied pin. -/
theorem common_sign_controlled (sign : EOSign)
    (hs : ∀i,EONegativeWitness.Supports sign (R.signature G i)) :
    C.ControlledCountingHard G := by
  classical
  by_cases hp : ∀i,GeneralEODEQProducer.Pure sign (G i)
  · intro α ea count w
    exact ⟨GeneralEOPureHardness.source G sign he hs hp negative w⟩
  · exact GeneralEOPhaseControlledNonpureSource.exists_nonpure_countingHard
      G sign he hs negative hp

include he in
/-- Opposite support failures have an actual controlled original-family exit,
including the ARS case; no final complexity assertion is a premise. -/
theorem support_failures_controlled (i j : Fin s)
    (hp : ¬EONegativeWitness.Supports .positive (R.signature G i))
    (hn : ¬EONegativeWitness.Supports .negative (R.signature G j)) :
    C.ControlledCountingHard G := by
  rcases GeneralEOPhaseControlledSource.family_outcome G he with pins | hard | ars
  · intro α ea count w
    exact ⟨GeneralEOPhaseSupportSource.source G
      (GeneralEONegativeSupportSource.select G i j (he i) (he j) hp hn)
      (Classical.choice pins) w⟩
  · exact hard
  · apply GeneralEOARSNonclosedSource.selected_controlled G i (he i) (ars i)
    intro closed
    apply hp
    intro x y z hx hy hz
    exact Or.inl (closed x y z hx hy hz)

include he negative in
/-- Universal negative EO hardness retains the full programme and length
control at the unchanged original finite family. All support, purity, ARS,
pinning, and nonzero side conditions are discharged inside the proof. -/
theorem controlled_hard : C.ControlledCountingHard G := by
  classical
  by_cases hp : ∀i,EONegativeWitness.Supports .positive (R.signature G i)
  · exact common_sign_controlled G he negative .positive hp
  by_cases hn : ∀i,EONegativeWitness.Supports .negative (R.signature G i)
  · exact common_sign_controlled G he negative .negative hn
  obtain ⟨i,hi⟩ := not_forall.mp hp
  obtain ⟨j,hj⟩ := not_forall.mp hn
  exact support_failures_controlled G he i j hi hj

variable {α : Type} {ea : Encoding α Bool} {count : α → ℕ}

/-- Every natural-number counting witness reduces to the original dictionary,
using precisely its original generated field and ordered-label answer codec. -/
def source (w : SharpPWitness ea count) : LengthControlledOracleReduction ea encodingNatBool
    (RawClosedNetwork.validatedEncoding s 1 a) (O.originalPresentation G).encoding
    count (O.originalValue G) :=
  Classical.choice (controlled_hard G he negative α ea count w)

include he negative in
theorem witnessCountingHard : Holant.LocalDrafts.CountingHardness.WitnessCountingHard
    (RawClosedNetwork.validatedEncoding s 1 a) (O.originalPresentation G).encoding
    (O.originalValue G) := by
  intro α ea count w
  exact ⟨(source G he negative w).reduction⟩

variable {Δ Q : Type} [Fintype Δ] [Fintype Q]
variable (m : Standard.Model Δ Q) (input : Bool → Δ) (hinj : Function.Injective input)
variable (clock : Polynomial ℕ) (htime : m.PolyTimeOn input clock)

/-- Conventional nondeterministic machine path counting uses the same source. -/
def standardSource : LengthControlledOracleReduction ea encodingNatBool
    (RawClosedNetwork.validatedEncoding s 1 a) (O.originalPresentation G).encoding
    (m.physicalCount (Standard.injectedEncoding ea input hinj)) (O.originalValue G) :=
  source G he negative (Standard.standard_to_witness (ea:=ea) m input hinj clock htime)


end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOUniversalSource
