import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralOddCompiler
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXLocalPinGraphs
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeSignedPortsCore

/-! Compile an actual odd-boundary resource and pin its first exposed port
with the retained physical pin. Every row and ordinary edge remains literal. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralOddPinGraph
open Holant Holant.Tractable
namespace M
export OrdinaryNegativeCubicGadgets (Macro)
export OrdinaryNegativeCubicGadgets.Macro (row row_denote)
export NoXLocalPinGraphs (pinFirst pinFirst_value output)
end M
namespace C
export NoXGeneralOddCompiler (output output_value)
end C
namespace D
export OrdinaryNegativeXUniversalResource (OddResource)
end D
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxRecDepth 32768
set_option Elab.async false
variable {K : IntermediateField ℚ AlgebraicComplex} {s n : ℕ} {a : ℕ→ℕ}
local instance : Algebra ℚ K := K.algebra'
variable (H : (j : Fin s)→Signature K (a j.val)) (e p0 p1 : Fin s)
variable (he : (⟨a e.val,H e⟩ : AnySignature K)=⟨4,Holant.EightVertex.ProductAnchor.equalityFour⟩)
variable (h0 : (⟨a p0.val,H p0⟩ : AnySignature K)=⟨1,OrdinaryNegativeSignedPortsCore.pin false⟩)
variable (h1 : (⟨a p1.val,H p1⟩ : AnySignature K)=⟨1,OrdinaryNegativeSignedPortsCore.pin true⟩)
variable (resource : D.OddResource (s:=s) a (n+1))

def compiled : M.Macro H (n+1) where
  network := (C.output H e p0 p1 he h0 h1 resource).network
  labels := (C.output H e p0 p1 he h0 h1 resource).labels
  exact := (C.output H e p0 p1 he h0 h1 resource).exact
  edges := (C.output H e p0 p1 he h0 h1 resource).ordinary

def pinMacro (bit : Bool) : M.Macro H 1 :=
  if bit then M.row p1 (OrdinaryNegativeSignedPortsCore.pin true) h1
    else M.row p0 (OrdinaryNegativeSignedPortsCore.pin false) h0

theorem pin_value (bit : Bool) : (pinMacro H p0 p1 h0 h1 bit).network.denote=
    fun x=>if x 0=bit then 1 else 0 := by
  cases bit <;> simp only [pinMacro,Bool.false_eq_true,ite_false,ite_true,M.row_denote]
  all_goals rfl

def output (bit : Bool) : NoXOrdinaryGraphAdjoin.Output H n :=
  M.output (M.pinFirst (compiled H e p0 p1 he h0 h1 resource) (pinMacro H p0 p1 h0 h1 bit))

theorem value (bit : Bool) (x : Fin n→Bool) :
    (output H e p0 p1 he h0 h1 resource bit).network.denote x=
      resource.signature H (Fin.cons bit x) := by
  change (M.pinFirst (compiled H e p0 p1 he h0 h1 resource) (pinMacro H p0 p1 h0 h1 bit)).network.denote x=_
  rw [M.pinFirst_value _ _ bit (pin_value H p0 p1 h0 h1 bit)]
  exact congrFun (C.output_value H e p0 p1 he h0 h1 resource) _

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralOddPinGraph
end
