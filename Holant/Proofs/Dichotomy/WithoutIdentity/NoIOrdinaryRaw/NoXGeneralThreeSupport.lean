import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralThreeSupportSource
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralNAND
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralEvenNAND
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.GenericOrdinarySource
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoXWeightedAntiResourcesOriginal
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.Target

/-! Direct three-supported binary endpoints over the exact generic ordinary
source: either a literal unsigned pin/identification minor, or any actual even
private block. Every zero position is handled without a literal anti row. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIOrdinaryRaw.NoXGeneralThreeSupport
open Holant Holant.Algebraic Holant.Tractable Holant.Complexity Computability
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace T
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionTensor (substitute)
end T
namespace O
export StableHigherCurrentOrdinarySquare (square)
export OrdinaryNegativeNANDMinorOriginal (square_pin)
end O
namespace D
export OrdinaryNegativeMixedBlockData (Recipe EvenRecipe)
export OrdinaryNegativeMixedBlockSource (trace)
end D
namespace B
export OrdinaryNegativeMixedBlockBinarySource (binary controlled)
end B
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 32768
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : NoIOrdinaryRaw.Target)
variable (src : NoIOrdinaryRaw.GenericOrdinarySource.Data G)
local instance : Algebra ℚ src.K := src.K.algebra'
variable {α : Type} {ea : Encoding α Bool} {count : α→ℕ}

namespace Minor
variable (j : Fin src.size) (q : Fin (src.b j.val)→Bool ⊕ Fin 2) (hole : Bool×Bool)
variable (zero : src.H j (T.substitute q ![hole.1,hole.2])=0)
variable (live : ∀x y,(x,y)≠hole→src.H j (T.substitute q ![x,y])≠0)

def source (w : SharpPWitness ea count) : PhysicalProgramme ea encodingNatBool
    G.inputEncoding
    G.outputEncoding count G.value :=
  PhysicalProgramme.ofControlled (Programme.compose
    (Programme.compose
      (NoXGeneralThreeSupportSource.source src.F (fun x y=>(src.H j (T.substitute q ![x,y]))^2)
        hole (by rw [zero];simp) (fun x y h=>pow_ne_zero 2 (live x y h)) w)
      (OrdinaryNegativeNANDMinorSource.controlled src.F (O.square src.H)
        j (src.p false) (src.p true) q
        (O.square_pin src.H (src.p false) false (src.hp false))
        (O.square_pin src.H (src.p true) true (src.hp true))))
    (NoIOrdinaryRaw.GenericOrdinarySource.squareCSPSource G src).controlled)

include zero live in
theorem countingHard : NoIOrdinaryRaw.NoXWeightedAntiResourcesOriginal.Hard G := by
  intro α ea count w
  exact ⟨(source G src j q hole zero live w).controlled⟩
end Minor

namespace EvenBlock
variable {k : ℕ} (rows : D.Recipe (u:=1) (s:=src.size) (a:=fun _=>2+k) (b:=src.b))
variable (balanced : D.EvenRecipe rows) (hole : Bool×Bool)
variable (zero : D.trace src.H k rows 0 ![hole.1,hole.2]=0)
variable (live : ∀x y,(x,y)≠hole→D.trace src.H k rows 0 ![x,y]≠0)

def source (w : SharpPWitness ea count) : PhysicalProgramme ea encodingNatBool
    G.inputEncoding
    G.outputEncoding count G.value :=
  PhysicalProgramme.ofControlled (Programme.compose
    (Programme.compose (NoXGeneralThreeSupportSource.source src.F (B.binary src.H k rows)
      hole zero live w)
      (B.controlled src.F src.H src.e (src.p false) (src.p true) src.he
        (src.hp false) (src.hp true) k rows balanced)) src.toOriginal)

include balanced zero live in
theorem countingHard : NoIOrdinaryRaw.NoXWeightedAntiResourcesOriginal.Hard G := by
  intro α ea count w
  exact ⟨(source G src rows balanced hole zero live w).controlled⟩
end EvenBlock


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIOrdinaryRaw.NoXGeneralThreeSupport
end
