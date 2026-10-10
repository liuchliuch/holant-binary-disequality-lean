import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2SignedSixSquare
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2OrdinaryTwist
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2OrdinaryPairOutcome

/-! A real four-copy Eq4 source for the sparse signed-six tensor. Two copies
form an EO generalized equality of weight b²+c²; two further copies align its
repeated port blocks. No physical X or phase gate is assumed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2SignedSparseEq4
open Holant Holant.Tractable Holant.Complexity
open Holant.LocalDrafts.RemoteWork.HardnessChainV1 OrdinaryNegativeCubicGadgets
namespace P
export GlobalCloseCompletionKleinOrdinaryPair (series seriesLabels series_exact series_ordinary)
end P
namespace T
export GlobalCloseCompletionKleinTwistedAlgebra (normal)
end T
namespace S
export GlobalCloseCompletionC2SignedSixSquare (signed)
end S
namespace Q
export GlobalCloseCompletionC2OrdinarySquare (square square_normal)
end Q
namespace O
export GlobalCloseCompletionC2OrdinaryDenseOrbit (swap_bc)
end O
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type} [Field K] [CharZero K] {r : ℕ} {b : ℕ→ℕ}
variable (H : (i : Fin r)→Signature K (b i.val))

def join (L R : Macro H 4) : Macro H 4 where
  network := P.series L.network (R.reindex (Equiv.swap 0 1)).network
  labels := P.seriesLabels L.network L.labels _ (R.reindex (Equiv.swap 0 1)).labels
  exact := P.series_exact H L.network L.labels _ (R.reindex (Equiv.swap 0 1)).labels L.exact (R.reindex (Equiv.swap 0 1)).exact
  edges := P.series_ordinary _ _ L.edges (R.reindex (Equiv.swap 0 1)).edges

theorem swap_eval (f : Signature K 4) (a b c d : Bool) :
    Tensor.reindex (Equiv.swap 0 1) f ![a,b,c,d]=f ![b,a,c,d] := by
  apply congrArg f
  funext i
  fin_cases i <;> rfl

theorem join_denote (L R : Macro H 4) (x : Fin 4→Bool) :
    (join H L R).network.denote x=
      (L.network.denote ![x 0,x 1,false,false]*R.network.denote ![false,false,x 2,x 3]+
       L.network.denote ![x 0,x 1,true,false]*R.network.denote ![true,false,x 2,x 3])+
      (L.network.denote ![x 0,x 1,false,true]*R.network.denote ![false,true,x 2,x 3]+
       L.network.denote ![x 0,x 1,true,true]*R.network.denote ![true,true,x 2,x 3]) := by
  change (P.series L.network (R.reindex (Equiv.swap 0 1)).network).denote x=_
  rw [GlobalCloseCompletionC2OrdinaryTwist.series_value,Macro.reindex_denote,
    swap_eval,swap_eval,swap_eval,swap_eval]

def order : Equiv.Perm (Fin 4) where
  toFun := ![2,0,1,3]
  invFun := ![1,2,0,3]
  left_inv := by decide
  right_inv := by decide

def transpose : Equiv.Perm (Fin 4) where
  toFun := ![2,3,0,1]
  invFun := ![2,3,0,1]
  left_inv := by decide
  right_inv := by decide

def gram (N : Macro H 4) : Macro H 4 := join H (N.reindex order) ((N.reindex order).reindex transpose)

theorem gram_denote (N : Macro H 4) (B C : K) (form : N.network.denote=S.signed B C 0) :
    (gram H N).network.denote=T.normal 0 0 (B^2+C^2) 0 := by
  funext x
  rw [gram,join_denote]
  simp only [Macro.reindex_denote,form]
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [Tensor.reindex,order,transpose,S.signed,T.normal,Holant.LocalDrafts.Hardness.EightVertexNonexception.table,h0,h1,h2,h3] <;> ring

def graph (N : Macro H 4) : Macro H 4 := Q.square H ((gram H N).reindex (Equiv.swap 1 2))

theorem graph_denote (N : Macro H 4) (B C : K) (form : N.network.denote=S.signed B C 0) :
    (graph H N).network.denote=(B^2+C^2)^2 • Holant.EightVertex.ProductAnchor.equalityFour := by
  have h : ((gram H N).reindex (Equiv.swap 1 2)).network.denote=T.normal 0 (B^2+C^2) 0 0 := by
    rw [Macro.reindex_denote,gram_denote H N B C form,O.swap_bc]
  have result := Q.square_normal H _ 0 (B^2+C^2) 0 0 h
  rw [show (graph H N).network.denote=(Q.square H ((gram H N).reindex (Equiv.swap 1 2))).network.denote from rfl,result]
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [T.normal,Holant.LocalDrafts.Hardness.EightVertexNonexception.table,
      Holant.EightVertex.ProductAnchor.equalityFour,Fin.forall_fin_succ,h0,h1,h2,h3]

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2SignedSparseEq4
end
