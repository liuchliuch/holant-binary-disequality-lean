import Holant.Proofs.Hardness.GeneralEONonARSPinningFieldBridge
import Holant.Proofs.Hardness.EOQuaternaryOriginalSource

/-! The hard alternative needed by the finite-phase part of MWX Theorem 27.
A quaternary macro is an actual original-labelled native-X graph. The complete
quaternary counting producer is compiled through that graph into the unchanged
original field. We do not infer a local directed pin, or identify hardness with
pinning equivalence through an unproved weighted counting upper bound. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEONonARSPinningSource
open Computability Holant Holant.Complexity Holant.Algebraic Holant.Tractable
open FixedGadgetSubstitution
namespace B
export GeneralEONonARSPinningFieldBridge
  (macroFamily macroPresentation macroValue presentation source query query_counts)
end B
namespace O
export Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalTarget
  (originalField originalPresentation originalValue)
end O
namespace C
export Holant.LocalDrafts.RemoteWork.PlatonicExits.PhysicalCost (composeControlled)
end C
namespace Standard
export Holant.LocalDrafts.MainChain.CBStandardNativeHardness.Standard
  (Model injectedEncoding standard_to_witness)
end Standard
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32768
attribute [local irreducible] EOQuaternaryOriginalSource.Family.source
  GeneralEONonARSPinningFieldBridge.source
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
variable (S : Network AlgebraicComplex 4) (SL : Labelling S.shape s 1 a)
variable (he : LabelledNetwork.Exact G S SL) (hn : ∀e,S.edge e=Signature.disequality)
variable (hc : Signature.CentralSupport S.denote) (ht : ¬EOTract {⟨4,S.denote⟩})
local instance targetAlgebra : Algebra ℚ (O.originalField G) := (O.originalField G).algebra'
variable {α : Type} {ea : Encoding α Bool} {f : α → ℕ}

include hc in
theorem eosupport : DenseEOUnitLocal.EOSupport S.denote := fun x hx => hc x (by omega)

def macroSource (w : SharpPWitness ea f) : LengthControlledOracleReduction ea encodingNatBool
    (RawClosedNetwork.validatedEncoding 1 1 (fun _ => 4)) (B.macroPresentation S).encoding
    f (B.macroValue S) :=
  EOQuaternaryOriginalSource.Family.source (a:=fun _ => 4) S.denote (eosupport S hc) ht
    (B.macroFamily S) 0 rfl w

def source (w : SharpPWitness ea f) : LengthControlledOracleReduction ea encodingNatBool
    (RawClosedNetwork.validatedEncoding s 1 a) (O.originalPresentation G).encoding
    f (O.originalValue G) :=
  C.composeControlled (macroSource S hc ht w) (B.source G S SL he hn)

include S SL he hn hc ht in
theorem witnessCountingHard : Holant.LocalDrafts.CountingHardness.WitnessCountingHard
    (RawClosedNetwork.validatedEncoding s 1 a) (O.originalPresentation G).encoding
    (O.originalValue G) := by
  intro α ea f w
  exact ⟨(source G S SL he hn hc ht w).reduction⟩

variable {Δ Q : Type} [Fintype Δ] [Fintype Q]
variable (m : Standard.Model Δ Q) (input : Bool → Δ) (hinj : Function.Injective input)
variable (clock : Polynomial ℕ) (htime : m.PolyTimeOn input clock)

def standardSource : LengthControlledOracleReduction ea encodingNatBool
    (RawClosedNetwork.validatedEncoding s 1 a) (O.originalPresentation G).encoding
    (m.physicalCount (Standard.injectedEncoding ea input hinj)) (O.originalValue G) :=
  source G S SL he hn hc ht (Standard.standard_to_witness (ea:=ea) m input hinj clock htime)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEONonARSPinningSource
