import Holant.Proofs.Hardness.GeneralEOARSNonclosedExtraction
import Holant.Proofs.Hardness.GeneralEODEQUnpinnedElimination

/-! Universal unpinned ARS/nonclosed-support counting source. Mating,
covariance selection, the free-pair exclusion, DEQ production and pin removal
are all derived; every oracle call uses the original finite family and codec. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOARSNonclosedSource
open Computability Holant Holant.Tractable Holant.Complexity
namespace P
export GeneralEOARSNonclosedPrefix (complex)
end P
namespace C
export GeneralEOPhaseExtractionControlledSource (ControlledCountingHard)
end C
namespace O
export Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalTarget (originalPresentation originalValue)
end O
namespace Standard
export Holant.LocalDrafts.MainChain.CBStandardNativeHardness.Standard
  (Model injectedEncoding standard_to_witness)
end Standard
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))

theorem selected_controlled (j : Fin s)
    (he : Signature.CentralSupport (G j))
    (ha : GeneralEOARSBoundary.ARSUpToScale (P.complex (G j)))
    (hc : ¬GeneralEONegativeClosedSupport.Closed (G j)) : C.ControlledCountingHard G := by
  rcases GeneralEOARSNonclosedExtraction.selected G j he ha hc with hard | produced
  · exact hard
  · obtain ⟨Q⟩ := produced
    exact GeneralEODEQUnpinnedElimination.controlled_hard G Q j he ha hc

variable (he : ∀i,Signature.CentralSupport (G i))
variable (ha : GeneralEOARSBoundary.FamilyARS (fun i => P.complex (G i)))
variable (hc : ¬∀i,GeneralEONegativeClosedSupport.Closed (G i))

include he ha hc in
theorem controlled_hard : C.ControlledCountingHard G := by
  classical
  obtain ⟨j,hj⟩ : ∃j,¬GeneralEONegativeClosedSupport.Closed (G j) := not_forall.mp hc
  exact selected_controlled G j (he j) (ha j) hj

variable {α : Type} {ea : Encoding α Bool} {count : α → ℕ}

/-- The selected machine is length controlled and has exactly the unchanged
original-family target encoding and coefficient answer presentation. -/
def source (w : SharpPWitness ea count) : LengthControlledOracleReduction ea encodingNatBool
    (RawClosedNetwork.validatedEncoding s 1 a) (O.originalPresentation G).encoding
    count (O.originalValue G) := Classical.choice (controlled_hard G he ha hc α ea count w)

include he ha hc in
theorem witnessCountingHard : GeneralEOPhaseExtractionSource.CountingHard G := by
  intro α ea count w
  exact ⟨(source G he ha hc w).reduction⟩

variable {Δ Q : Type} [Fintype Δ] [Fintype Q]
variable (m : Standard.Model Δ Q) (input : Bool → Δ) (hinj : Function.Injective input)
variable (clock : Polynomial ℕ) (htime : m.PolyTimeOn input clock)

def standardSource : LengthControlledOracleReduction ea encodingNatBool
    (RawClosedNetwork.validatedEncoding s 1 a) (O.originalPresentation G).encoding
    (m.physicalCount (Standard.injectedEncoding ea input hinj)) (O.originalValue G) :=
  source G he ha hc (Standard.standard_to_witness (ea:=ea) m input hinj clock htime)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOARSNonclosedSource
