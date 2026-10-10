import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeMixedBlockPrivateComposeSource

/-! Arbitrary fixed gadgets over genuine even resources flatten to genuine
even resources. Heterogeneous private variables are preserved and summed once;
no parity assumption is needed on the outer semantic recipe. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralEvenCompose
open Holant Holant.Tractable
open OrdinaryNegativeMixedBlockData
namespace C
export OrdinaryNegativeMixedBlockPrivateComposeCore (privateCount recipe node scope ports_eq)
export OrdinaryNegativeMixedBlockCompose (substitute even_map even_flatMap)
end C
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
set_option maxHeartbeats 1000000
set_option maxRecDepth 32768
set_option Elab.async false
variable {v s n l : ℕ} {b c : ℕ→ℕ}
variable (outer : Recipe (u:=1) (s:=v) (a:=fun _=>n+l) (b:=b))
variable (blocks : (j : Fin v)→B.Block (s:=s) (b:=c) (b j.val))

def counts (j : Fin v) : ℕ := (blocks j).privateCount

def inner (j : Fin v) : Recipe (u:=1) (s:=s) (a:=fun _=>b j.val+counts blocks j) (b:=c) :=
  (blocks j).rows

theorem balanced : EvenRecipe (C.recipe outer (counts blocks) (inner blocks)) := by
  intro i q
  rw [C.ports_eq]
  apply C.even_flatMap
  intro j _ p
  exact C.even_map _ ((blocks (C.node outer j).1).balanced 0) _ p

def block : B.Block (s:=s) (b:=c) n where
  privateCount := C.privateCount (n:=n) (l:=l) outer (counts blocks)
  rows := C.recipe (n:=n) (l:=l) outer (counts blocks) (inner blocks)
  balanced := balanced outer blocks

variable {K : Type} [Field K] (H : (j : Fin s)→Signature K (c j.val))

def family (j : Fin v) : Signature K (b j.val) := (blocks j).signature H

theorem block_value (z : Fin n→Bool) :
    (block outer blocks).signature H z=M.trace (a:=fun _=>n) (family blocks H) l outer 0 z :=
  V.trace_eq (n:=n) (l:=l) (b:=b) (c:=c) outer (counts blocks) (inner blocks) H z


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralEvenCompose
end
