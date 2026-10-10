import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralEvenDiagonalRawValue
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralEvenDiagonalRoot
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXOrdinaryGraphAdjoin
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryTargetInterpolationDiagonal
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralUnsignedBinary

/-! Every actual unary even block has an actual ordinary diagonal macro.
The literal unary values occur on its two equal boundary words, with no scale.
In particular, pinning a full even binary supplies its first-row diagonal. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralEvenDiagonal
open Holant Holant.Tractable Holant.Complexity
open Holant.Certificates.MatchingContractionClosure
open OrdinaryNegativeCubicGadgets
namespace B
export OrdinaryNegativeSparseMixingSource (Block)
end B
namespace R
export NoXGeneralEvenDiagonalRawValue (sourceInput sourceVariable conditional)
end R
namespace D
export NoXGeneralEvenDiagonalRoot (graph value)
end D
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 32768
set_option Elab.async false
variable {K : Type} [Field K] {s : ℕ} {a : ℕ→ℕ}
variable (H : (i : Fin s)→Signature K (a i.val)) (e p0 p1 : Fin s)
variable (he : (⟨a e.val,H e⟩ : AnySignature K)=⟨4,Holant.EightVertex.ProductAnchor.equalityFour⟩)
variable (h0 : (⟨a p0.val,H p0⟩ : AnySignature K)=⟨1,Holant.LocalDrafts.RemoteWork.CountingBridge.Gates.pin false⟩)
variable (h1 : (⟨a p1.val,H p1⟩ : AnySignature K)=⟨1,Holant.LocalDrafts.RemoteWork.CountingBridge.Gates.pin true⟩)
variable (row : B.Block (s:=s) (b:=a) 1)

def graph : Macro H 2 := D.graph H e he (R.sourceInput H row p0 p1 h0 h1) (R.sourceVariable H row p0 p1 h0 h1)

theorem value (x : Fin 2→Bool) : (graph H e p0 p1 he h0 h1 row).network.denote x=
    if x 0=x 1 then row.signature H (fun _=>x 0) else 0 := by
  rw [graph,D.value]
  unfold NoXGeneralEvenDiagonalRoot.conditional
  rw [R.conditional]

def output : NoXOrdinaryGraphAdjoin.Output H 2 where
  network:=(graph H e p0 p1 he h0 h1 row).network
  labels:=(graph H e p0 p1 he h0 h1 row).labels
  exact:=(graph H e p0 p1 he h0 h1 row).exact
  ordinary:=(graph H e p0 p1 he h0 h1 row).edges

theorem diagonal : (output H e p0 p1 he h0 h1 row).network.denote=
    binarySignature (OrdinaryTargetInterpolationDiagonal.diagonal
      (row.signature H (fun _=>false)) (row.signature H (fun _=>true))) := by
  funext x
  rw [show (output H e p0 p1 he h0 h1 row).network=(graph H e p0 p1 he h0 h1 row).network from rfl,value]
  cases hx : x 0 <;> cases hy : x 1 <;> simp [binarySignature,OrdinaryTargetInterpolationDiagonal.diagonal,hx,hy]

def firstRow (f : B.Block (s:=s) (b:=a) 2) : B.Block (s:=s) (b:=a) 1 :=
  NoXGeneralUnsignedBinary.restrict f (![.inl false,.inr 0])

theorem firstRow_value (f : B.Block (s:=s) (b:=a) 2) (x : Fin 1→Bool) :
    (firstRow f).signature H x=f.signature H ![false,x 0] := by
  rw [firstRow,NoXGeneralUnsignedBinary.restrict_value]
  congr 1
  funext i
  fin_cases i <;> rfl

def binaryOutput (f : B.Block (s:=s) (b:=a) 2) : NoXOrdinaryGraphAdjoin.Output H 2 :=
  output H e p0 p1 he h0 h1 (firstRow f)

theorem binary_diagonal (f : B.Block (s:=s) (b:=a) 2) :
    (binaryOutput H e p0 p1 he h0 h1 f).network.denote=
      binarySignature (OrdinaryTargetInterpolationDiagonal.diagonal
        (f.signature H ![false,false]) (f.signature H ![false,true])) := by
  rw [binaryOutput,diagonal,firstRow_value,firstRow_value]


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralEvenDiagonal
end
