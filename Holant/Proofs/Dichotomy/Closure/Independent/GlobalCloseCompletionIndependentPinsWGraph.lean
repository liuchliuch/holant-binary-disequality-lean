import Holant.Proofs.Dichotomy.Closure.Independent.GlobalCloseCompletionIndependentPinsWCore
import Holant.Proofs.Dichotomy.Closure.Ternary.GlobalCloseCompletionTernaryGHZGraph
import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryIsotropicSource

/-! Physical symmetric-W escape. The ordinary triangle or the same triangle
with one retained Z on each internal edge produces an actual symmetric GHZ
signature. The choice is made from the nonzero repeated column, and the
semantic output matrix uses certified algebraic roots. No matrix is inserted
as a vertex. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIndependentPinsWGraph
open Holant Holant.Tractable
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open scoped BigOperators
open OrdinaryNegativeCubicGadgets
namespace W
export GlobalCloseCompletionIndependentPinsWCore
  (w image image_eq sign twist gram core columns columns_determinant coordinate triangle_image
    choose_phase roots core_ghz)
end W
namespace T
export GlobalCloseCompletionTernaryGHZCore (triangle action)
end T
namespace C
export GlobalCloseCompletionSymmetricGHZCoordinates (ghz eq3)
end C
namespace B
export Holant.Tractable.SymmetricBinaryPullback (determinant determinant_ne_zero invertibleOfDeterminant)
end B
namespace Z
export GlobalCloseCompletionUnaryIsotropicSource (z)
end Z
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type} [Field K] {s : ℕ} {a : ℕ→ℕ}
variable {H : (i : Fin s)→Signature K (a i.val)}

def order : Equiv.Perm (Fin 5) := Equiv.ofBijective
  (![2,0,4,1,3] : Fin 5→Fin 5) (by decide)

def decorate (N : Macro H 3) (Z : Macro H 2) : Macro H 3 :=
  ((N.tensor Z).reindex order).contract

theorem decorate_value (N : Macro H 3) (D : Macro H 2) (form : D.network.denote=Z.z) :
    (decorate N D).network.denote=W.twist (-1) N.network.denote := by
  funext x
  rw [decorate,Macro.contract_denote]
  simp only [Macro.reindex_denote,Macro.tensor_denote,Tensor.reindex_apply,Signature.tensor_apply,form]
  have first (v : Bool) :
      (fun i : Fin 3=>(Fin.cons v (Fin.cons v x) : Fin 5→Bool) (order (Fin.castAdd 2 i)))=![x 0,v,x 2] := by
    funext i
    fin_cases i <;> rfl
  have second (v : Bool) :
      (fun i : Fin 2=>(Fin.cons v (Fin.cons v x) : Fin 5→Bool) (order (Fin.natAdd 3 i)))=![v,x 1] := by
    funext i
    fin_cases i <;> rfl
  simp only [first,second]
  have word : ![x 0,x 1,x 2]=x := by funext i;fin_cases i <;> rfl
  cases h : x 1
  · simp only [Z.z,Matrix.cons_val_zero,Matrix.cons_val_one,h,Bool.false_eq_true,
      Bool.true_eq_false,ite_false,ite_true,mul_one,mul_zero,add_zero,W.twist,W.sign,one_mul]
    congr 1
    funext i
    fin_cases i <;> simp [h]
  · simp only [Z.z,Matrix.cons_val_zero,Matrix.cons_val_one,h,Bool.false_eq_true,
      Bool.true_eq_false,ite_false,ite_true,mul_one,mul_zero,zero_add,W.twist,W.sign,neg_one_mul,mul_neg_one]
    congr 1
    congr 1
    funext i
    fin_cases i <;> simp [h]

def graph (N : Macro H 3) (D : Macro H 2) (v : Bool) : Macro H 3 :=
  GlobalCloseCompletionTernaryGHZGraph.triangle (if v then decorate N D else N)

theorem graph_value (N : Macro H 3) (D : Macro H 2) (form : D.network.denote=Z.z) (v : Bool) :
    (graph N D v).network.denote=T.triangle (W.twist (if v then -1 else 1) N.network.denote) := by
  cases v
  · rw [graph,if_neg Bool.false_ne_true,GlobalCloseCompletionTernaryGHZGraph.value]
    congr 1
    funext x
    simp [W.twist,W.sign]
  · rw [graph,if_pos rfl,GlobalCloseCompletionTernaryGHZGraph.value,decorate_value N D form]
    rfl

theorem map_triangle (phi : K→+*AlgebraicComplex) (f : Signature K 3) :
    RingHomRealization.mapSignature phi (T.triangle f)=T.triangle (RingHomRealization.mapSignature phi f) := by
  funext x
  simp only [RingHomRealization.mapSignature,T.triangle,map_sum,map_mul]

theorem map_twist (phi : K→+*AlgebraicComplex) (t : K) (f : Signature K 3) :
    RingHomRealization.mapSignature phi (W.twist t f)=W.twist (phi t) (RingHomRealization.mapSignature phi f) := by
  funext x
  cases h : x 1 <;> simp [RingHomRealization.mapSignature,W.twist,W.sign,h]

theorem graph_mapped (phi : K→+*AlgebraicComplex) (N : Macro H 3) (D : Macro H 2)
    (form : D.network.denote=Z.z) (v : Bool) :
    RingHomRealization.mapSignature phi (graph N D v).network.denote=
      T.triangle (W.twist (if v then -1 else 1) (RingHomRealization.mapSignature phi N.network.denote)) := by
  rw [graph_value N D form v,map_triangle,map_twist]
  cases v <;> simp

/-- Every invertible symmetric W decomposition has one actual GHZ output;
the isotropic repeated-vector case uses the retained Z vertices. -/
theorem produces (phi : K→+*AlgebraicComplex) (N : Macro H 3) (D : Macro H 2)
    (form : D.network.denote=Z.z) (A : InvertibleKernel)
    (wForm : RingHomRealization.mapSignature phi N.network.denote=A.action W.w) :
    ∃v : Bool,∃R : InvertibleKernel,
      RingHomRealization.mapSignature phi (graph N D v).network.denote=C.ghz R.matrix := by
  obtain ⟨v,hv⟩:=W.choose_phase A.matrix (B.determinant_ne_zero A)
  let t : AlgebraicComplex:=if v then -1 else 1
  have ht : t≠0 := by cases v <;> norm_num [t]
  let p:=W.gram t A.matrix false false
  let q:=W.gram t A.matrix false true
  let r:=W.gram t A.matrix true true
  obtain ⟨d,c,hd,hc,square,cube⟩:=W.roots A t ht hv
  have determinant : B.determinant (W.columns p q d c)≠0 := by
    rw [B.determinant,W.columns_determinant]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hc)) hv) hd
  let S : InvertibleKernel:=B.invertibleOfDeterminant (W.columns p q d c) determinant
  refine ⟨v,A.comp S,?_⟩
  rw [graph_mapped phi N D form v,wForm]
  change T.triangle (W.twist t (Signature.coordinateAction (fun _=>A.matrix) W.w))=_
  rw [←W.image_eq,W.triangle_image]
  change T.action (Matrix.of A.matrix) (W.core p q r)=_
  rw [←W.coordinate,W.core_ghz p q r d c square cube]
  change Signature.coordinateAction (fun _=>A.matrix)
    (Signature.coordinateAction (fun _=>S.matrix) C.eq3)=
      Signature.coordinateAction (fun _=>Kernel.mul A.matrix S.matrix) C.eq3
  exact Signature.coordinateAction_comp _ _ _

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIndependentPinsWGraph
end
