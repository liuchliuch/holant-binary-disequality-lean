import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeMixedBlockSource
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeMixedBlockInput
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeNANDTable

/-! Every actual positive binary block has an unsigned raw-CSP source in the
same fixed field. The binary signature is the block's actual private trace;
there is no supplied virtual sign action, field map, or hardness premise. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeMixedBlockBinarySource
open Computability Holant Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace D
export OrdinaryNegativeMixedBlockData (Recipe EvenRecipe Input inputEncoding)
end D
namespace M
export OrdinaryNegativeMixedBlockSource (trace privateValue privateControlled)
end M
namespace I
export OrdinaryNegativeMixedBlockInput (query queryComputes value)
end I
namespace N
export OrdinaryNegativeNANDTable (query queryComputes query_value)
end N
namespace P
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryCSPProgrammeValidated (Input inputEncoding)
end P
namespace V
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryCSPProgrammeValue (value)
end V
namespace E
export StableHigherCurrentEvenCSPSource (tables)
end E
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false

variable {K : Type} [Field K] [Algebra ℚ K] {d s : ℕ} {b : ℕ→ℕ}
variable (F : FixedField K d) (H : (j : Fin s)→Signature K (b j.val))
variable (e p0 p1 : Fin s)
variable (he : (⟨b e.val,H e⟩ : AnySignature K)=⟨4,Holant.EightVertex.ProductAnchor.equalityFour⟩)
variable (h0 : (⟨b p0.val,H p0⟩ : AnySignature K)=⟨1,Holant.LocalDrafts.RemoteWork.CountingBridge.Gates.pin false⟩)
variable (h1 : (⟨b p1.val,H p1⟩ : AnySignature K)=⟨1,Holant.LocalDrafts.RemoteWork.CountingBridge.Gates.pin true⟩)
variable (k : ℕ) (blocks : D.Recipe (u:=1) (s:=s) (a:=fun _=>2+k) (b:=b))
variable (balanced : D.EvenRecipe blocks)

def binary (x y : Bool) : K := M.trace H k blocks 0 ![x,y]
def value (r : P.Input) : K := V.value (binary H k blocks) r.val

def query (r : P.Input) : D.Input (u:=1) (a:=fun _=>2) :=
  I.query (N.query (a:=fun _=>2) (0 : Fin 1) rfl r)

def queryComputes : Computes P.inputEncoding (D.inputEncoding (u:=1) (a:=fun _=>2)) query :=
  (N.queryComputes (a:=fun _=>2) (0 : Fin 1) rfl).andThen I.queryComputes

omit [Algebra ℚ K] in
theorem query_value (r : P.Input) : M.privateValue H k blocks (query r)=value H k blocks r := by
  unfold M.privateValue query
  rw [I.value]
  exact N.query_value (a:=fun _=>2) (0 : Fin 1) (M.trace H k blocks)
    (M.trace H k blocks 0) rfl r

def toMixed : LengthControlledOracleReduction P.inputEncoding F.encoding
    (D.inputEncoding (u:=1) (a:=fun _=>2)) F.encoding
    (value H k blocks) (M.privateValue H k blocks) :=
  controlledOneQueryOfEq queryComputes (identityComputes F.encoding)
    (M.privateControlled F H e p0 p1 he h0 h1 k blocks balanced).sourceOutputBound
    (value H k blocks) (fun r=>(query_value H k blocks r).symm)

def controlled : LengthControlledOracleReduction P.inputEncoding F.encoding
    (RawClosedNetwork.validatedEncoding s 1 b) F.encoding
    (value H k blocks) ((E.tables F H).evaluate F) :=
  Programme.compose (toMixed F H e p0 p1 he h0 h1 k blocks balanced)
    (M.privateControlled F H e p0 p1 he h0 h1 k blocks balanced)

def physical : PhysicalProgramme P.inputEncoding F.encoding
    (RawClosedNetwork.validatedEncoding s 1 b) F.encoding
    (value H k blocks) ((E.tables F H).evaluate F) :=
  PhysicalProgramme.ofControlled (controlled F H e p0 p1 he h0 h1 k blocks balanced)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeMixedBlockBinarySource
end
