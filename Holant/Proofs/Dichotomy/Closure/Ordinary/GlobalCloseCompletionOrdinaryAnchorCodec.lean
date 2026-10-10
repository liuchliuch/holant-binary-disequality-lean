import Holant.Proofs.Dichotomy.Closure.Ordinary.GlobalCloseCompletionOrdinaryAnchorInput
import Holant.Proofs.Algorithms.FieldCodec

/-! Exact native-lift-to-original-G programme for the ordinary anchor input.
Graph bytes and all ordered incidences are unchanged. The answer conversion
is the existing fixed rational linear machine between the two actual fields;
no equality of generated coefficient fields is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOrdinaryAnchorCodec
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace I
export GlobalCloseCompletionOrdinaryAnchorInput (Input mapped native)
end I
namespace O
export Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalTarget
  (originalField originalPresentation originalValue target_exact)
end O
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
variable (D : I.Input G)
local instance : Algebra ℚ D.K := D.K.algebra'
abbrev tables := QuaternaryOrdinaryCompanion.tables D.F D.H
abbrev value := (tables G D).evaluate D.F
abbrev field := O.originalField (I.native G D)
local instance : Algebra ℚ (field G D) := (field G D).algebra'
abbrev presentation := O.originalPresentation (I.native G D)
abbrev nativeValue := O.originalValue (I.native G D)
abbrev inputEncoding := RawClosedNetwork.validatedEncoding D.count 1 D.b

theorem mapped_value (r : ExactSignatureTables.Input D.count 1 D.b) :
    D.K.val.toRingHom (value G D r)=
      (r.val.realize r.property (I.mapped G D) KSourceTransport.equalityEdges).denote Fin.elim0 := by
  change D.K.val.toRingHom ((tables G D).evaluate D.F r)=_
  rw [ExactSignatureTables.evaluate_eq_decoded]
  simp only [tables,QuaternaryOrdinaryCompanion.tables,LinearEquiv.apply_symm_apply]
  rw [←Network.denote_map D.K.val.toRingHom]
  congr 1
  unfold Network.map RawClosedNetwork.realize
  congr 1
  funext e b c
  cases b <;> cases c <;> simp [KSourceTransport.equalityEdges,Signature.equality]

theorem native_value (r : ExactSignatureTables.Input D.count 1 D.b) :
    (nativeValue G D r : AlgebraicComplex)=D.K.val.toRingHom (value G D r) := by
  have h := KSourceTransport.value_exact (I.mapped G D) r
  rw [OriginalFamily.value_exact,OriginalFamily.value_exact] at h
  exact (O.target_exact (I.native G D) r).trans (h.trans (mapped_value G D r).symm)

def recover : D.K→ₗ[ℚ] (field G D) :=
  (field G D).val.toLinearMap.leftInverse.comp D.K.val.toLinearMap

def recoverComputes : Computes D.F.encoding (presentation G D).encoding (recover G D) :=
  FieldCodec.computes D.F (presentation G D) (recover G D)

theorem recover_value (r : ExactSignatureTables.Input D.count 1 D.b) :
    nativeValue G D r=recover G D (value G D r) := by
  change nativeValue G D r=(field G D).val.toLinearMap.leftInverse (D.K.val.toRingHom (value G D r))
  rw [←native_value G D r]
  exact (FieldCodec.retract_embedding (field G D).val (nativeValue G D r)).symm

def nativeToOrdinary : LengthControlledOracleReduction
    (inputEncoding G D) (presentation G D).encoding (inputEncoding G D) D.F.encoding
    (nativeValue G D) (value G D) :=
  controlledOneQueryOfEq (identityComputes (inputEncoding G D)) (recoverComputes G D)
    ((tables G D).outputBound D.F) (nativeValue G D) (recover_value G D)

def toOriginal := Programme.compose (nativeToOrdinary G D) D.toOriginal


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOrdinaryAnchorCodec
end
