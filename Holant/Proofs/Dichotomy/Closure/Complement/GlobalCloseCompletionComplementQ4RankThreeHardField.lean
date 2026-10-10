import Holant.Proofs.Dichotomy.Main.PaperTerminalBridgeCancellationField
import Holant.Proofs.Hardness.ComplexNonselfdualSource

/-! Dense EO hardness in an arbitrary fixed number-field codec. The complex
source and both actual generated-field answer conversions are composed; no
hardness or coefficient-transport premise is supplied. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4RankThreeHardField
open Computability Holant Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace D
export DenseEOUnitLocal (EOSupport NonzeroMiddle)
end D
namespace C
export PaperTerminalBridgeCancellationField (embedding algebraic mapped_source)
end C
namespace O
export Holant.LocalDrafts.Hardness.EightVertexNonexception.Source (targetEncoding)
end O
namespace S
export NativeAntiTargetSource (base Output)
end S
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type} [Field K] [NumberField K] {degree : ℕ}
variable (F : FixedField K degree) (M : Signature K 4)
variable (eo : D.EOSupport M) (dense : D.NonzeroMiddle M)

include eo in
theorem mapped_eo : D.EOSupport (SignatureFieldMap.mapped M (C.embedding (K:=K))) := by
  intro x hx
  change C.embedding (M x)=0
  rw [eo x hx,map_zero]

include dense in
theorem mapped_dense : D.NonzeroMiddle (SignatureFieldMap.mapped M (C.embedding (K:=K))) := by
  rcases dense with ⟨hb,hc,hd,hw,hz,hy⟩
  exact ⟨(map_ne_zero (C.embedding (K:=K))).mpr hb,
    (map_ne_zero (C.embedding (K:=K))).mpr hc,(map_ne_zero (C.embedding (K:=K))).mpr hd,
    (map_ne_zero (C.embedding (K:=K))).mpr hw,(map_ne_zero (C.embedding (K:=K))).mpr hz,
    (map_ne_zero (C.embedding (K:=K))).mpr hy⟩

variable {α : Type} {ea : Encoding α Bool} {f : α→ℕ}
def source (w : SharpPWitness ea f) : LengthControlledOracleReduction ea encodingNatBool
    O.targetEncoding F.encoding f ((S.base (fun _ : Fin 1=>M) F).evaluate F) :=
  Programme.compose
    (ComplexNonselfdualSource.source (SignatureFieldMap.mapped M (C.embedding (K:=K)))
      (SignatureFieldMap.mapped_algebraic M (C.algebraic M) (C.embedding (K:=K)))
      (mapped_eo M eo) (mapped_dense M dense) w)
    (C.mapped_source F M)

variable {s : ℕ} {a : ℕ→ℕ}
variable (H : (i : Fin s)→Signature K (a i.val)) (N : S.Output H 4)
def actual (eo : D.EOSupport N.network.denote) (dense : D.NonzeroMiddle N.network.denote)
    (w : SharpPWitness ea f) : LengthControlledOracleReduction ea encodingNatBool
    (RawClosedNetwork.validatedEncoding s 1 a) F.encoding f ((S.base H F).evaluate F) :=
  Programme.compose (source F N.network.denote eo dense w) (PaperTerminalBridgeMacroAccess.source H F N)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4RankThreeHardField
end
