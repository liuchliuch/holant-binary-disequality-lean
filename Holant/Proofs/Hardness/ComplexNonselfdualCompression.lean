import Holant.Proofs.Hardness.ExactTwoChain
import Holant.Proofs.Hardness.LabelledNetwork

/-! Literal two-copy compression of arbitrary EO data. Both vertices are the
original tensor; the second has port order [1,0,3,2]. The output has only one
possibly asymmetric opposite pair. This local normal form makes no universal
hardness assertion. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.ComplexNonselfdualCompression
open Holant Holant.Complexity FixedGadgetSubstitution
open Holant.LocalDrafts.Hardness.EightVertexNonexception
namespace R
export Holant.Complexity.BinaryInterpolation.Chains (reindex reindex_denote)
end R
set_option backward.isDefEq.respectTransparency false
variable {K : Type} [Field K]

def order : Equiv.Perm (Fin 4) where
  toFun := ![1,0,3,2]
  invFun := ![1,0,3,2]
  left_inv := by decide
  right_inv := by decide

def network (M : Signature K 4) : Network K 4 :=
  ExactTwoChain.series (Network.corolla M) (R.reindex (Network.corolla M) order)

def compressed (M : Signature K 4) : Signature K 4 :=
  let e := entries M
  table ⟨0,2*e.b*e.d,e.c*e.z,e.b*e.y+e.d*e.w,
    e.b*e.y+e.d*e.w,e.c*e.z,2*e.w*e.y,0⟩

/-- All sixteen assignments are evaluated from the actual two native-X
contractions, with no assumed transfer-matrix semantics. -/
theorem denote_table (b c d w z y : K) :
    (network (table ⟨0,b,c,d,w,z,y,0⟩)).denote=
      table ⟨0,2*b*d,c*z,b*y+d*w,b*y+d*w,c*z,2*w*y,0⟩ := by
  funext x
  rw [network,ExactTwoChain.series_denote]
  simp only [Network.denote_corolla,R.reindex_denote,Tensor.reindex_apply]
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [table,order,h0,h1,h2,h3] <;> ring

theorem denote (M : Signature K 4) (he : DenseEOUnitLocal.EOSupport M) :
    (network M).denote=compressed M := by
  have hz := DenseEOUnitLocal.corners_zero M he
  have ht : M=table ⟨0,(entries M).b,(entries M).c,(entries M).d,
      (entries M).w,(entries M).z,(entries M).y,0⟩ := by
    conv_lhs => rw [←table_entries M (DenseEOUnitLocal.even M he)]
    congr 1
    ext <;> simp only [hz.1,hz.2]
  calc
    _=(network (table ⟨0,(entries M).b,(entries M).c,(entries M).d,
      (entries M).w,(entries M).z,(entries M).y,0⟩)).denote := congrArg (fun q=>(network q).denote) ht
    _=compressed M := denote_table _ _ _ _ _ _

/-- The same literal contraction accepts an already constructed network. -/
def compressNetwork (N : Network K 4) : Network K 4 :=
  ExactTwoChain.series N (R.reindex N order)

theorem compressNetwork_denote (N : Network K 4) (M : Signature K 4)
    (hN : N.denote=M) (he : DenseEOUnitLocal.EOSupport M) :
    (compressNetwork N).denote=compressed M := by
  rw [←denote M he]
  funext x
  simp only [compressNetwork,network,ExactTwoChain.series_denote,R.reindex_denote,
    Network.denote_corolla,hN]

theorem compressed_entries (M : Signature K 4) :
    entries (compressed M)=⟨0,2*(entries M).b*(entries M).d,
      (entries M).c*(entries M).z,(entries M).b*(entries M).y+(entries M).d*(entries M).w,
      (entries M).b*(entries M).y+(entries M).d*(entries M).w,
      (entries M).c*(entries M).z,2*(entries M).w*(entries M).y,0⟩ := rfl

theorem compressed_eo (M : Signature K 4) : DenseEOUnitLocal.EOSupport (compressed M) := by
  intro x hx
  rw [Holant.EightVertex.ProductAnchor.weight_four] at hx
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3
  all_goals try norm_num [h0,h1,h2,h3] at hx
  all_goals simp [compressed,table,h0,h1,h2,h3]

theorem one_asymmetric_pair (M : Signature K 4) :
    (entries (compressed M)).d=(entries (compressed M)).w ∧
    (entries (compressed M)).c=(entries (compressed M)).z := ⟨rfl,rfl⟩

theorem compressed_middle [CharZero K] (M : Signature K 4)
    (hm : DenseEOUnitLocal.NonzeroMiddle M)
    (hs : (entries M).b*(entries M).y+(entries M).d*(entries M).w≠0) :
    DenseEOUnitLocal.NonzeroMiddle (compressed M) := by
  rcases hm with ⟨hb,hc,hd,hw,hz,hy⟩
  exact ⟨mul_ne_zero (mul_ne_zero (by norm_num) hb) hd,mul_ne_zero hc hz,hs,hs,
    mul_ne_zero hc hz,mul_ne_zero (mul_ne_zero (by norm_num) hw) hy⟩

theorem balanced_selfdual (M : Signature K 4)
    (hb : (entries M).b*(entries M).d=(entries M).w*(entries M).y) :
    (entries (compressed M)).b=(entries (compressed M)).y := by
  change 2*(entries M).b*(entries M).d=2*(entries M).w*(entries M).y
  calc
    _=2*((entries M).b*(entries M).d) := by ring
    _=2*((entries M).w*(entries M).y) := by rw [hb]
    _=_ := by ring

def labels (M : Signature K 4) : Labelling (network M).shape 1 1 (fun _=>4) where
  vertex _ := 0
  vertex_arity v := by fin_cases v <;> rfl
  edge _ := 0
abbrev template (M : Signature K 4) := (labels M).template

theorem valid (M : Signature K 4) : (template M).WellFormed 1 1 (fun _=>4) :=
  (labels M).wellFormed

theorem counts (M : Signature K 4) :
    (template M).vertices.length=2 ∧ (template M).edges.length=2 := ⟨rfl,rfl⟩

def rows : List (ℕ × List (ℕ ⊕ (ℕ × Bool))) :=
  [(0,[.inl 0,.inr (1,false),.inl 2,.inr (0,false)]),
   (0,[.inl 1,.inr (1,true),.inl 3,.inr (0,true)])]

theorem records (M : Signature K 4) :
    (template M).boundary=4 ∧ (template M).vertices=rows ∧ (template M).edges=[0,0] :=
  ⟨rfl,rfl,rfl⟩

theorem template_denote (M : Signature K 4) (he : DenseEOUnitLocal.EOSupport M) :
    ((template M).network (valid M) (fun _ : Fin 1=>M)
      (fun _ : Fin 1=>Signature.disequality)).denote=compressed M := by
  rw [←denote M he]
  apply Labelling.denote_template_of_labels (labels M) _ _ (network M).vertex (network M).edge
  · intro v x; fin_cases v <;> rfl
  · intro e x y; fin_cases e <;> rfl

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.ComplexNonselfdualCompression
