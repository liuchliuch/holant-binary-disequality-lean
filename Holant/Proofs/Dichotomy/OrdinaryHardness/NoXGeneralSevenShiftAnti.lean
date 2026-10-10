import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralSevenShiftSemantics

/-! Every non-dual shifted seven-port simplex resource gives an actual
full anti: compile the old recipe, permute its exposed ports, pin three
literal bits, and contract one equal pair. The original oracle is unchanged. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralSevenShiftAnti
open Holant Holant.Tractable
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace P
export NoXGeneralSevenShiftPlan (classIndex pin order input wire NonDual)
end P
namespace S
export NoXGeneralSevenShiftSemantics (binary left right left_nonzero right_nonzero anti)
end S
namespace M
export OrdinaryNegativeCubicGadgets (Macro)
export OrdinaryNegativeCubicGadgets.Macro (reindex reindex_denote contract contract_denote)
export NoXLocalPinGraphs (pinFirst pinFirst_value output)
export NoXGeneralOddPinGraph (pinMacro pin_value)
end M
namespace C
export NoXGeneralOddCompiler (graph value)
export NoXReciprocalMixedProjectionCore (logical)
export OrdinaryNegativeSparseMixingAlpha (codeSeven)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 32768
set_option Elab.async false
section Graph
variable {K : IntermediateField ℚ AlgebraicComplex} {s : ℕ} {b : ℕ→ℕ}
local instance : Algebra ℚ K:=K.algebra'
variable (H : (j : Fin s)→Signature K (b j.val)) (e p0 p1 : Fin s)
variable (he : (⟨b e.val,H e⟩ : AnySignature K)=⟨4,Holant.EightVertex.ProductAnchor.equalityFour⟩)
variable (h0 : (⟨b p0.val,H p0⟩ : AnySignature K)=⟨1,OrdinaryNegativeSignedPortsCore.pin false⟩)
variable (h1 : (⟨b p1.val,H p1⟩ : AnySignature K)=⟨1,OrdinaryNegativeSignedPortsCore.pin true⟩)
variable (row : OrdinaryNegativeXUniversalResource.OddResource (s:=s) b 7) (sign : Fin 7→Bool)

def pinned : M.Macro H 4:=
  M.pinFirst (M.pinFirst (M.pinFirst
    ((C.graph H e p0 p1 he h0 h1 row).reindex (P.order (P.classIndex sign)).symm)
    (M.pinMacro H p0 p1 h0 h1 (P.pin (P.classIndex sign) 0)))
    (M.pinMacro H p0 p1 h0 h1 (P.pin (P.classIndex sign) 1)))
    (M.pinMacro H p0 p1 h0 h1 (P.pin (P.classIndex sign) 2))

def graph : M.Macro H 2:=(pinned H e p0 p1 he h0 h1 row sign).contract

theorem pinned_value (x : Fin 4→Bool) :
    (pinned H e p0 p1 he h0 h1 row sign).network.denote x=
      row.signature H (fun j=>(Fin.cons (P.pin (P.classIndex sign) 0)
        (Fin.cons (P.pin (P.classIndex sign) 1) (Fin.cons (P.pin (P.classIndex sign) 2) x)) : Fin 7→Bool)
          ((P.order (P.classIndex sign)).symm j)):=by
  rw [pinned,M.pinFirst_value _ _ _ (M.pin_value H p0 p1 h0 h1 (P.pin (P.classIndex sign) 2)),
    M.pinFirst_value _ _ _ (M.pin_value H p0 p1 h0 h1 (P.pin (P.classIndex sign) 1)),
    M.pinFirst_value _ _ _ (M.pin_value H p0 p1 h0 h1 (P.pin (P.classIndex sign) 0)),M.reindex_denote]
  change (C.graph H e p0 p1 he h0 h1 row).network.denote _=_
  rw [C.value]

theorem value (x : Fin 2→Bool) :
    (graph H e p0 p1 he h0 h1 row sign).network.denote x=S.binary H row sign x:=by
  rw [graph,M.contract_denote,pinned_value,pinned_value]
  have cons (t : Bool) :
      Fin.cons (P.pin (P.classIndex sign) 0) (Fin.cons (P.pin (P.classIndex sign) 1)
        (Fin.cons (P.pin (P.classIndex sign) 2) (Fin.cons t (Fin.cons t x))))=
          P.input (P.classIndex sign) t x:=by
    funext i
    fin_cases i <;> rfl
  simp_rw [cons]
  rfl
end Graph

section Terminal
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
variable (src : GenericOrdinarySource.Data G)
local instance : Algebra ℚ src.K:=src.K.algebra'
variable (row : OrdinaryNegativeXUniversalResource.OddResource (s:=src.size) src.b 7)
variable (sign : Fin 7→Bool)
variable (support : ∀z,row.ambient src.H z≠0 ↔ ∃x : Fin 3→Bool,C.logical sign z=C.codeSeven x)
variable (nondual : P.NonDual sign)
variable (negative : StableHigherCurrentOrdinaryTerminal.Obstruction (preprocess (GenericOrdinarySource.family G src)))

include support nondual negative in
theorem countingHard : NoXWeightedAntiResourcesOriginal.Hard G:=by
  let N:=graph src.H src.e (src.p false) (src.p true) src.he (src.hp false) (src.hp true) row sign
  let out:=M.output N
  apply NoXGeneralGraphAnti.countingHard G src out (S.left src.H row sign) (S.right src.H row sign)
    (S.left_nonzero src.H row sign support nondual) (S.right_nonzero src.H row sign support nondual) _ negative
  calc out.network.denote=S.binary src.H row sign:=
      funext (value src.H src.e (src.p false) (src.p true) src.he (src.hp false) (src.hp true) row sign)
    _= _:=S.anti src.H row sign support nondual
end Terminal

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralSevenShiftAnti
end
