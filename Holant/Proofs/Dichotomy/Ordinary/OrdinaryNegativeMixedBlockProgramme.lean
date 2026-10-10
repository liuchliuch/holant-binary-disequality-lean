import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeMixedBlockData

/-! Actual mixed-label block writer. All finite recipes are compiled into
the program; input rows, labels and scope addresses are read from their real
framed tapes. Two constant addresses and four literal pin rows are emitted. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeMixedBlockProgramme
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.LocalDrafts.TetrahedralCompletion.EvenCSPReduction
open OrdinaryNegativeMixedBlockData
namespace C
export GeneralEOPairedCSPFamilyRaw (Raw encoding labelEncoding addressesEncoding variablesComputes)
end C
namespace B
export GeneralEOPairedFamilyBundleRaw (dataEncoding dataComputes)
end B
namespace P
export GeneralEOPairedCSPFamilyProgramme (labelRecodeComputes)
end P
namespace W
export Holant.LocalDrafts.Tractability.AffineMachine.WireLists (mapComputes append succComputes)
end W
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

variable {u s : ℕ} {a b : ℕ→ℕ}
variable (recipe : Recipe (u:=u) (s:=s) (a:=a) (b:=b)) (p₀ p₁ : Fin s)

def factorComputes : Computes (pairEncoding (C.labelEncoding s) C.addressesEncoding)
    Raw.factorEncoding (factor (s:=s)) :=
  recode (pairComputes
    ((Wiring.firstComputes (C.labelEncoding s) C.addressesEncoding).andThen
      (P.labelRecodeComputes encodingNatBool Fin.val))
    (Wiring.secondComputes (C.labelEncoding s) C.addressesEncoding))
    id (fun _=>rfl) (fun _=>rfl)

def rowsComputes : Computes (C.encoding u) (framedListEncoding Raw.factorEncoding)
    (fun r=>(OrdinaryNegativeMixedBlockData.B.data (s:=u) (t:=s) (a:=fun k=>a k*2) (b:=fun k=>b k*2) (family u a) (family s b) recipe r).map factor) :=
  (B.dataComputes (s:=u) (t:=s) (a:=fun k=>a k*2) (b:=fun k=>b k*2) (family u a) (family s b) recipe).andThen
    (W.mapComputes (pairEncoding (C.labelEncoding s) C.addressesEncoding)
      Raw.factorEncoding factor factorComputes)

def rawComputes : Computes (C.encoding u) Raw.encoding (raw recipe p₀ p₁) :=
  recode (pairComputes
    ((C.variablesComputes.andThen W.succComputes).andThen W.succComputes)
    ((pairComputes (rowsComputes recipe)
      (constantComputes (C.encoding u) (framedListEncoding Raw.factorEncoding) (guards p₀ p₁))).andThen
      (W.append Raw.factorEncoding)))
    id (fun _=>rfl) (fun _=>rfl)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeMixedBlockProgramme
end
