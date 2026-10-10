import Holant.Proofs.Dichotomy.Closure.Paired.GlobalCloseCompletionPairedSeriesCore
import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryZeroCapTrees
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryTargetInterpolationDiagonal

/-! Literal binary loop and pin0 caps of a paired row. Both copies of the
actual scalar pin remain in the coefficient; no logical variable is erased. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionPairedSeriesCaps
open Holant Holant.Tractable
open Holant.Certificates.MatchingContractionClosure
namespace M
export OrdinaryNegativeCubicGadgets (Macro)
export OrdinaryNegativeCubicGadgets.Macro (contract_denote reindex_denote)
end M
namespace Z
export GlobalCloseCompletionUnaryZeroCapTrees (output graph value permutation)
end Z
namespace P
export GlobalCloseCompletionPairedSeriesCore (row)
end P
namespace D
export OrdinaryTargetInterpolationDiagonal (diagonal)
end D
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
set_option Elab.async false
variable {K : Type} [Field K] {s n : ℕ} {a : ℕ→ℕ}
variable {H : (i : Fin s)→Signature K (a i.val)}

def output (N : M.Macro H n) : NoXOrdinaryGraphAdjoin.Output H n :=
  ⟨N.network,N.labels,N.exact,N.edges⟩

def cap (U : M.Macro H 1) (N : M.Macro H (n+1)) (i : Fin (n+1)) : M.Macro H n :=
  let V:=Z.output H (output U) (output N) i
  ⟨V.network,V.labels,V.exact,V.ordinary⟩

theorem cap_value (U : M.Macro H 1) (N : M.Macro H (n+1)) (c : K)
    (h0 : U.network.denote (fun _=>false)=c) (h1 : U.network.denote (fun _=>true)=0)
    (i : Fin (n+1)) (x : Fin n→Bool) :
    (cap U N i).network.denote x=c*N.network.denote (fun j=>(Fin.cons false x : Fin (n+1)→Bool) (Equiv.swap 0 i j)) :=
  Z.value H (output U) (output N) c h0 h1 i x

def rowCap (U : M.Macro H 1) (N : M.Macro H 4) : M.Macro H 2 := cap U (cap U N 0) 1

theorem rowCap_value (U : M.Macro H 1) (N : M.Macro H 4) (c : K)
    (h0 : U.network.denote (fun _=>false)=c) (h1 : U.network.denote (fun _=>true)=0)
    (B : Matrix Bool Bool K) (hN : N.network.denote=P.row B) :
    (rowCap U N).network.denote=binarySignature (D.diagonal (c^2*B false false) (c^2*B false true)) := by
  funext x
  rw [rowCap,cap_value U (cap U N 0) c h0 h1,cap_value U N c h0 h1,hN]
  have hw : (fun j : Fin 4=>(Fin.cons false
      (fun k : Fin 3=>(Fin.cons false x : Fin 3→Bool) (Equiv.swap 0 1 k)) : Fin 4→Bool)
      (Equiv.swap 0 0 j))=![false,x 0,false,x 1] := by
    funext j
    fin_cases j <;> rfl
  rw [hw]
  cases hx0 : x 0 <;> cases hx1 : x 1 <;>
    simp [P.row,D.diagonal,binarySignature,hx0,hx1,pow_two,mul_assoc]

theorem loop_value (N : M.Macro H 4) (B : Matrix Bool Bool K) (hN : N.network.denote=P.row B) :
    N.contract.network.denote=binarySignature (D.diagonal (B false false) (B true true)) := by
  funext x
  rw [M.contract_denote,hN]
  cases hx0 : x 0 <;> cases hx1 : x 1 <;>
    simp [P.row,D.diagonal,binarySignature,hx0,hx1]

def transposePorts : Equiv.Perm (Fin 4) where
  toFun:=![1,0,3,2]
  invFun:=![1,0,3,2]
  left_inv:=by decide
  right_inv:=by decide

theorem transpose_value (N : M.Macro H 4) (B : Matrix Bool Bool K) (hN : N.network.denote=P.row B) :
    (N.reindex transposePorts).network.denote=P.row B.transpose := by
  rw [M.reindex_denote,hN]
  funext x
  cases hx0 : x 0 <;> cases hx1 : x 1 <;> cases hx2 : x 2 <;> cases hx3 : x 3 <;>
    simp [Tensor.reindex,P.row,transposePorts,Matrix.transpose_apply,hx0,hx1,hx2,hx3]


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionPairedSeriesCaps
end
