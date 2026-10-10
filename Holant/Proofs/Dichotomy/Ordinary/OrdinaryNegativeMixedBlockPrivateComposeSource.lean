import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeMixedBlockPrivateComposeValue
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeSparseMixingSource

/-! Heterogeneous private odd resources feed an even outer recipe as a real
ordinary Block. Existing checked Block programmes then compile every emitted
row into the unchanged target H with its original fixed-field answer codec. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeMixedBlockPrivateComposeSource
open Holant Holant.Algebraic
open OrdinaryNegativeMixedBlockData OrdinaryNegativeMixedBlockPrivateComposeCore
namespace P
export OrdinaryNegativeMixedBlockPrivateComposeParity (even_recipe)
end P
namespace V
export OrdinaryNegativeMixedBlockPrivateComposeValue (rows trace_eq)
end V
namespace B
export OrdinaryNegativeSparseMixingSource (Block)
end B
namespace M
export OrdinaryNegativeMixedBlockSource (trace)
end M
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
variable {v s n l : ℕ} {b c : ℕ→ℕ}
variable (outer : Recipe (u:=1) (s:=v) (a:=fun _=>n+l) (b:=b))
variable (k : Fin v→ℕ)
variable (inner : (j : Fin v)→Recipe (u:=1) (s:=s) (a:=fun _=>b j.val+k j) (b:=c))
variable (hi : OddPrivate k inner) (ho : EvenRecipe outer)

def block : B.Block (s:=s) (b:=c) n where
  privateCount := privateCount (n:=n) (l:=l) outer k
  rows := recipe (n:=n) (l:=l) outer k inner
  balanced := P.even_recipe (n:=n) (l:=l) outer k inner hi ho

variable {K : Type} [Field K] (H : (j : Fin s)→Signature K (c j.val))

theorem block_value (z : Fin n→Bool) :
    (block outer k inner hi ho).signature H z=M.trace (a:=fun _=>n) (V.rows (b:=b) (c:=c) k inner H) l outer 0 z :=
  V.trace_eq (n:=n) (l:=l) (b:=b) (c:=c) outer k inner H z

variable [Algebra ℚ K] {d : ℕ} (F : FixedField K d) (e p₀ p₁ : Fin s)
variable (he : (⟨c e.val,H e⟩ : AnySignature K)=⟨4,Holant.EightVertex.ProductAnchor.equalityFour⟩)
variable (h₀ : (⟨c p₀.val,H p₀⟩ : AnySignature K)=⟨1,Holant.LocalDrafts.RemoteWork.CountingBridge.Gates.pin false⟩)
variable (h₁ : (⟨c p₁.val,H p₁⟩ : AnySignature K)=⟨1,Holant.LocalDrafts.RemoteWork.CountingBridge.Gates.pin true⟩)

/-- Physical ordinary source for the complete flattened block. -/
def source := (block outer k inner hi ho).physical H F e p₀ p₁ he h₀ h₁

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeMixedBlockPrivateComposeSource
end
