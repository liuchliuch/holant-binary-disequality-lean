import Holant.Proofs.Hardness.GeneralEOPairedFamilyExtractionSupportGeometry
import Holant.Proofs.Hardness.GeneralEOPairedFamilyExtractionChoice

/-! The accepted internal orientation puts the origin in every compressed
support. Nonclosure under coordinatewise intersection then extracts a literal
ternary parity support using only identifications and a false constant. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionSupport
open Holant Holant.Tractable
namespace N
export GeneralEONegativeClosedSupport (data pairing covers Closed mem_points)
end N
namespace C
export Holant.LocalDrafts.Tractability.EOEvaluation.PairingConstruction (Side pairing port_false)
end C
namespace L
export Holant.LocalDrafts.Tractability.EOEvaluation.PairLift (compress word_compress)
end L
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false

variable {n : ℕ}

theorem pairing_origin (f : Signature AlgebraicComplex n) (he : Signature.CentralSupport f)
    (hn : f≠0) (hc : N.Closed f) :
    (N.pairing f he hn hc).word origin=(N.data f he hn hc).base.val := by
  let D := N.data f he hn hc
  have hh : L.compress (N.pairing f he hn hc) D.base.val=origin := by
    funext j
    exact ((Fintype.equivFin (C.Side D false)).symm j).property
  rw [←hh]
  exact L.word_compress _ _ (N.covers f he hn hc _ ((N.mem_points f _).mp D.base.property))

theorem compressed_origin_nonzero (f : Signature AlgebraicComplex n)
    (he : Signature.CentralSupport f) (hn : f≠0) (hc : N.Closed f) :
    (N.pairing f he hn hc).restrict f origin≠0 := by
  change f ((N.pairing f he hn hc).word origin)≠0
  rw [pairing_origin]
  exact (N.mem_points f _).mp (N.data f he hn hc).base.property


theorem xorClosed_of_closed (f : Signature AlgebraicComplex n) (h0 : f origin≠0)
    (hc : N.Closed f) : XorClosed f := by
  intro u v hu hv
  have hh : f (tripleXor u v origin)≠0 := hc u v origin hu hv h0
  have he : tripleXor u v origin=xor u v := by
    funext i
    simp [tripleXor,origin,xor]
  exact he ▸ hh

theorem compressed_xorClosed (f : Signature AlgebraicComplex n)
    (he : Signature.CentralSupport f) (hn : f≠0) (hc : N.Closed f) :
    XorClosed ((N.pairing f he hn hc).restrict f) :=
  xorClosed_of_closed _ (compressed_origin_nonzero f he hn hc)
    (GeneralEOPairedFamilyExtractionChoice.restrict_closed _ _ hc)


end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionSupport
