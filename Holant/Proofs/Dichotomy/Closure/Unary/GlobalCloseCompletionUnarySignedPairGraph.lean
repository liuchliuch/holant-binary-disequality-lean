import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnarySignedPairAlgebra
import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryBothPinFactors
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinOrdinaryAttach

/-! Actual same-table graphs square signed pairs, expose their supported
binary columns with the two literal pins, and apply a real weighted-anti
binary at any boundary. Every unary multiplier remains in the matrix. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnarySignedPairGraph
open Holant Holant.Tractable Holant.Complexity FixedGadgetSubstitution
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.LocalDrafts.Hardness.GeneralExtraction.NamedContraction
open OrdinaryNegativeCubicGadgets
namespace A
export GlobalCloseCompletionUnarySignedPairAlgebra (row square anti flipSite corrected corrected_value)
end A
namespace P
export GlobalCloseCompletionPairedSeriesCore (series)
end P
namespace F
export GlobalCloseCompletionUnaryBothPinFactors (graph word value uses ordinary)
end F
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option Elab.async false
variable {K : Type} [Field K] {r : ℕ} {a : ℕ→ℕ}
variable {H : (j : Fin r)→Signature K (a j.val)}

def mates : Equiv.Perm (Fin 4) := Equiv.ofBijective (![1,0,3,2] : Fin 4→Fin 4) (by decide)
def bundles : Equiv.Perm (Fin 4) := Equiv.ofBijective (![2,3,0,1] : Fin 4→Fin 4) (by decide)

def squared (N : Macro H 4) : Macro H 4 := P.series N (N.reindex mates)

theorem squared_value (N : Macro H 4) (B : Matrix Bool Bool K) (e₀ e₁ : Bool)
    (form : N.network.denote=A.row B e₀ e₁) :
    (squared N).network.denote=A.row (A.square B false false) false false := by
  funext x
  rw [squared,P.series,GlobalCloseCompletionUnaryOrdinaryEquality.series_value,
    Macro.reindex_denote,form]
  simp only [Tensor.reindex_apply]
  have reorder (u v : Bool) : (fun i=>(![u,x 1,v,x 3] : Fin 4→Bool) (mates i))=![x 1,u,x 3,v] := by
    funext i;fin_cases i <;>rfl
  simp_rw [reorder]
  cases e₀ <;>cases e₁ <;>cases h0 : x 0 <;>cases h1 : x 1 <;>cases h2 : x 2 <;>cases h3 : x 3 <;>
    simp [A.row,A.square,Fintype.sum_bool,h0,h1,h2,h3,pow_two]

variable (pins : Bool→Macro H 1)

def capNetwork (N : Macro H 4) (e : Bool) : Network K 2 :=
  F.graph (fun v=>(pins v).network) 2 2 ![false,e] N.network

def capLabels (N : Macro H 4) (e : Bool) : Labelling (capNetwork pins N e).shape r 1 a :=
  let h:=F.uses (fun v=>(pins v).network) (Set.range fun j : Fin r=>(⟨a j.val,H j⟩ : AnySignature K))
    (fun v w=>⟨(pins v).labels.vertex w,(pins v).exact w⟩) 2 2 ![false,e] N.network
    (fun v=>⟨N.labels.vertex v,N.exact v⟩)
  {vertex v:=Classical.choose (h v)
   vertex_arity v:=congrArg Sigma.fst (Classical.choose_spec (h v))
   edge _:=0}

def cap (N : Macro H 4) (e : Bool) : Macro H 2 where
  network:=capNetwork pins N e
  labels:=capLabels pins N e
  exact v:=Classical.choose_spec (F.uses (fun v=>(pins v).network)
    (Set.range fun j : Fin r=>(⟨a j.val,H j⟩ : AnySignature K))
    (fun v w=>⟨(pins v).labels.vertex w,(pins v).exact w⟩) 2 2 ![false,e] N.network
    (fun v=>⟨N.labels.vertex v,N.exact v⟩) v)
  edges:=F.ordinary (fun v=>(pins v).network) (fun v=>(pins v).edges) 2 2 ![false,e] N.network N.edges

variable (pinsForm : ∀v,(pins v).network.denote=QuaternaryUnaryAccess.pin v)
include pinsForm in
theorem cap_value (N : Macro H 4) (B : Matrix Bool Bool K) (e : Bool)
    (form : N.network.denote=A.row B true e) :
    (cap pins N e).network.denote=A.anti (fun b=>B b false) := by
  funext x
  change (capNetwork pins N e).denote x=_
  rw [capNetwork,F.value _ pinsForm,form]
  have word : F.word x 2 ![false,e]=![x 0,x 1,false,e] := by
    funext i;fin_cases i <;>rfl
  rw [word]
  cases e <;>cases h0 : x 0 <;>cases h1 : x 1 <;>simp [A.row,A.anti,h0,h1]

theorem transpose_value (N : Macro H 4) (B : Matrix Bool Bool K) (e₀ e₁ : Bool)
    (form : N.network.denote=A.row B e₀ e₁) :
    (N.reindex bundles).network.denote=A.row B.transpose e₁ e₀ := by
  rw [Macro.reindex_denote,form]
  funext x
  cases e₀ <;>cases e₁ <;>cases h0 : x 0 <;>cases h1 : x 1 <;>cases h2 : x 2 <;>cases h3 : x 3 <;>
    simp [A.row,Tensor.reindex,Matrix.transpose_apply,bundles,h0,h1,h2,h3]

def middle (N : Macro H 4) (D : Macro H 2) : Macro H 4 :=
  ((N.tensor D).reindex (GlobalCloseCompletionSparseEq4Flip.order false)).contract

theorem middle_value (N : Macro H 4) (D : Macro H 2) (q : Bool→K)
    (form : D.network.denote=A.anti q) : (middle N D).network.denote=A.flipSite N.network.denote q 1 := by
  funext x
  rw [middle,Macro.contract_denote,Macro.reindex_denote,Macro.tensor_denote,form]
  simp only [Tensor.reindex_apply,Signature.tensor_apply]
  have left (v : Bool) : (fun i : Fin 4=>(Fin.cons v (Fin.cons v x) : Fin 6→Bool)
      ((GlobalCloseCompletionSparseEq4Flip.order false) (Fin.castAdd 2 i)))=Function.update x 1 v := by
    funext i;fin_cases i <;>simp [GlobalCloseCompletionSparseEq4Flip.order,Function.update] <;>rfl
  have right (v : Bool) : (fun i : Fin 2=>(Fin.cons v (Fin.cons v x) : Fin 6→Bool)
      ((GlobalCloseCompletionSparseEq4Flip.order false) (Fin.natAdd 4 i)))=![x 1,v] := by
    funext i;fin_cases i <;>rfl
  simp only [left,right]
  cases h : x 1 <;>simp [A.anti,A.flipSite,h,mul_comm]

def attach (N : Macro H 4) (D : Macro H 2) (i : Fin 4) : Macro H 4 :=
  (middle (N.reindex (Equiv.swap 1 i)) D).reindex (Equiv.swap 1 i)

theorem attach_value (N : Macro H 4) (D : Macro H 2) (q : Bool→K) (i : Fin 4)
    (form : D.network.denote=A.anti q) : (attach N D i).network.denote=A.flipSite N.network.denote q i := by
  rw [attach,Macro.reindex_denote,middle_value _ D q form,Macro.reindex_denote]
  funext x
  simp only [Tensor.reindex_apply,A.flipSite,Equiv.swap_apply_left,Equiv.swap_apply_right]
  congr 1
  apply congrArg N.network.denote
  funext j
  by_cases hj : j=i
  · subst j;simp [Function.update]
  · have different : (Equiv.swap (1 : Fin 4) i) j≠1 := by
      intro equal
      exact hj (by have h:=congrArg (Equiv.swap (1 : Fin 4) i) equal;simpa using h)
    simp [Function.update,different,hj]

def correct (N : Macro H 4) (D : Macro H 2) (e₀ e₁ : Bool) : Macro H 4 :=
  let N':=if e₀ then attach N D 1 else N
  if e₁ then attach N' D 3 else N'

theorem correct_value (N : Macro H 4) (D : Macro H 2) (B : Matrix Bool Bool K) (q : Bool→K)
    (e₀ e₁ : Bool) (form : N.network.denote=A.row B e₀ e₁) (antiForm : D.network.denote=A.anti q) :
    (correct N D e₀ e₁).network.denote=A.row (A.corrected B q e₀ e₁) false false := by
  have h:=A.corrected_value B q e₀ e₁
  cases e₀ <;>cases e₁ <;>simp only [correct,Bool.false_eq_true,ite_false,ite_true] at h ⊢ <;>
    try simp_rw [attach_value _ D q _ antiForm,form]
  all_goals try rw [form]
  all_goals exact h


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnarySignedPairGraph
end
