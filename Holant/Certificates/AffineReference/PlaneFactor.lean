import Holant.Certificates.AffineReference.Plane
import Holant.Certificates.AffineReference.FullEvenExit

namespace Holant.Certificates.AffineReference
open Holant Holant.Tractable Holant.Certificates.TwelveLoops Holant.Certificates.FourthRootOdd
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

 def blockTensor (b : Fin 3) (A B C D : AlgebraicComplex) : Signature AlgebraicComplex 4 := fun x =>
  if OnPlane b x then
    if x (blockPair b).1 then if x (blockComplement b).1 then D else C
    else if x (blockComplement b).1 then B else A
  else 0

 theorem blockTensor_chart (b : Fin 3) (A B C D : AlgebraicComplex) (y : Fin 2 → Bool) :
    blockTensor b A B C D (planeChart b y)=
      if y 0 then if y 1 then D else C else if y 1 then B else A := by
  fin_cases b <;> simp [blockTensor,OnPlane,planeChart,blockPair,blockComplement]

 theorem plane_reconstruction (h : Signature AlgebraicComplex 4) (b : Fin 3) (hs : PlaneSupport h b) :
    h=blockTensor b (planeTable h b ![false,false]) (planeTable h b ![false,true])
      (planeTable h b ![true,false]) (planeTable h b ![true,true]) := by
  funext x
  by_cases hx : OnPlane b x
  · have H := planeChart_original b x hx
    conv_lhs => rw [←H]
    rw [blockTensor]
    simp only [if_pos hx]
    unfold planeTable
    cases h0 : x (blockPair b).1 <;> cases h1 : x (blockComplement b).1 <;> simp [h0,h1]
  · have hz : h x=0 := by by_contra hn;exact hx ((hs x).mp hn)
    simp [blockTensor,hx,hz]

 def sigmaTwoPorts : (Σ _ : Fin 2,Fin 2) ≃ Fin 4 where
  toFun p := ⟨p.1.val*2+p.2.val,by omega⟩
  invFun p := ⟨⟨p.val/2,by omega⟩,⟨p.val%2,by omega⟩⟩
  left_inv := by decide
  right_inv := by decide

 def twoEqualityDecomposition (b : Fin 3) (a r t : AlgebraicComplex) (ha : a≠0) :
    TensorDecomposition AlgebraicComplex 4 where
  count := 2
  arity := fun _ => 2
  factor := fun i => weightedEquality (if i=0 then r else t)
  ports := sigmaTwoPorts.trans (portEquiv (initialPair b))
  scale := Units.mk0 a ha

 theorem twoEqualityDecomposition_value (b : Fin 3) (a r t : AlgebraicComplex) (ha : a≠0) :
    (twoEqualityDecomposition b a r t ha).value=
      fun x => a*Tensor.reindex (portEquiv (initialPair b))
        (Signature.tensor (weightedEquality r) (weightedEquality t)) x := by
  funext x
  simp [TensorDecomposition.value,twoEqualityDecomposition,Fin.prod_univ_two,
    Tensor.reindex,Signature.tensor_apply,sigmaTwoPorts,ha]
  apply congrArg₂ (·*·)
  · apply congrArg (weightedEquality r)
    funext j
    fin_cases j <;> rfl
  · apply congrArg (weightedEquality t)
    funext j
    fin_cases j <;> rfl

 theorem weightedEquality_endpoints (r : AlgebraicComplex) (y : Fin 2 → Bool) :
    weightedEquality r y=(if y=(fun _ => false) then 1 else 0)+(if y=(fun _ => true) then r else 0) := by
  have hy : y=![y 0,y 1] := by funext i;fin_cases i <;> rfl
  rw [hy]
  cases y 0 <;> cases y 1 <;> simp [weightedEquality,funext_iff,Fin.forall_fin_two]

 theorem twoEqualityDecomposition_weighted (b : Fin 3) (a r t : AlgebraicComplex)
    (ha : a≠0) (hr : r≠0) (ht : t≠0) :
    EightVertex.ProductAnchor.TwoWeightedEqualities (twoEqualityDecomposition b a r t ha).value := by
  refine ⟨twoEqualityDecomposition b a r t ha,rfl,fun _ => rfl,rfl,?_,?_⟩
  · intro i
    fin_cases i <;> simp [twoEqualityDecomposition,weightedEquality,hr,ht]
  · intro i y
    change weightedEquality _ y=_
    rw [weightedEquality_endpoints]
    simp [twoEqualityDecomposition,weightedEquality]

 theorem blockTensor_factor (b : Fin 3) (A B C D : AlgebraicComplex)
    (hA : A≠0) (hB : B≠0) (hC : C≠0) (h : A*D=B*C) :
    EightVertex.ProductAnchor.TwoWeightedEqualities (blockTensor b A B C D) := by
  have H := twoEqualityDecomposition_weighted b A (C/A) (B/A) hA
    (div_ne_zero hC hA) (div_ne_zero hB hA)
  have he : (twoEqualityDecomposition b A (C/A) (B/A) hA).value=blockTensor b A B C D := by
    rw [twoEqualityDecomposition_value]
    funext x
    fin_cases b <;>
      simp [blockTensor,OnPlane,Tensor.reindex,Signature.tensor_apply,weightedEquality,
        portEquiv,portOrder,initialPair,blockPair,blockComplement] <;>
      split_ifs <;> simp_all <;> field_simp [hA] <;> linear_combination -h
  rwa [he] at H

end
end Holant.Certificates.AffineReference
