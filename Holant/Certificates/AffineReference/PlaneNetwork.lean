import Holant.Certificates.AffineReference.PlaneFactor
import Holant.Certificates.FourthRootOdd.TwoCopyNetwork
import Holant.EightVertex.ProductAnchor.MonomialCase

/-! The support-four negative cross-ratio branch uses two original copies and
corresponding native-X wires on the selected complementary two-port block. -/
namespace Holant.Certificates.AffineReference
open Holant Holant.Tractable Holant.Certificates.TwelveLoops Holant.Certificates.FourthRootOdd
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000

 def complementaryPair (b : Fin 3) : Fin 6 := ⟨5-b.val,by omega⟩

 theorem support_four_two_copy (b : Fin 3) (A B C D : AlgebraicComplex) :
    twoCopy (blockTensor b A B C D) (complementaryPair b)=
      blockTensor 0 (2*A*B) (A*D+B*C) (A*D+B*C) (2*C*D) := by
  funext x
  fin_cases b <;> cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3
  all_goals simp [twoCopy,blockTensor,OnPlane,insertPair,firstHalf,secondHalf,
    portEquiv,portInverse,complementaryPair,blockPair,blockComplement,h0,h1,h2,h3]
  all_goals ring

 theorem diagonal_block_pure (A D : AlgebraicComplex) (hA : A≠0) (hD : D≠0) :
    EightVertex.ProductAnchor.PureEquality (blockTensor 0 A 0 0 D) := by
  refine ⟨A,D,hA,hD,?_⟩
  funext x
  have hx : x=![x 0,x 1,x 2,x 3] := by funext i;fin_cases i <;> rfl
  rw [hx]
  cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;>
    simp [blockTensor,OnPlane,blockPair,blockComplement,EightVertex.ProductAnchor.ge4,
      Tractable.complementWord,funext_iff,Fin.forall_fin_succ]

 theorem plane_negative_exit (h : Signature AlgebraicComplex 4) (b : Fin 3)
    (hs : PlaneSupport h b)
    (hneg : planeTable h b ![false,false]*planeTable h b ![true,true]=
      -(planeTable h b ![false,true]*planeTable h b ![true,false])) :
    EightVertex.ProductAnchor.PureEquality (twoCopyNative h (complementaryPair b)) ∧
      Gadget.Realizes ({⟨4,h⟩} : SignatureFamily AlgebraicComplex) .disequality
        (twoCopyNative h (complementaryPair b)) := by
  refine ⟨?_,twoCopy_realizes _ _⟩
  rw [twoCopyNative_eq,plane_reconstruction h b hs,support_four_two_copy]
  have hz : planeTable h b ![false,false]*planeTable h b ![true,true]+
      planeTable h b ![false,true]*planeTable h b ![true,false]=0 := by linear_combination hneg
  rw [hz]
  exact diagonal_block_pure _ _
    (mul_ne_zero (mul_ne_zero (by norm_num) (planeTable_nonzero h b hs _)) (planeTable_nonzero h b hs _))
    (mul_ne_zero (mul_ne_zero (by norm_num) (planeTable_nonzero h b hs _)) (planeTable_nonzero h b hs _))

 theorem plane_positive_factor (h : Signature AlgebraicComplex 4) (b : Fin 3)
    (hs : PlaneSupport h b)
    (hpos : planeTable h b ![false,false]*planeTable h b ![true,true]=
      planeTable h b ![false,true]*planeTable h b ![true,false]) :
    EightVertex.ProductAnchor.TwoWeightedEqualities h := by
  rw [plane_reconstruction h b hs]
  exact blockTensor_factor b _ _ _ _ (planeTable_nonzero h b hs _)
    (planeTable_nonzero h b hs _) (planeTable_nonzero h b hs _) hpos

 theorem support_four_reference_exits (h : Signature AlgebraicComplex 4) (b : Fin 3)
    (ha : Affine h) (hs : PlaneSupport h b) :
    (planeTable h b ![false,false]*planeTable h b ![true,true]/
      (planeTable h b ![false,true]*planeTable h b ![true,false])=1 ∨
     planeTable h b ![false,false]*planeTable h b ![true,true]/
      (planeTable h b ![false,true]*planeTable h b ![true,false])= -1) ∧
    (EightVertex.ProductAnchor.TwoWeightedEqualities h ∨
      (EightVertex.ProductAnchor.PureEquality (twoCopyNative h (complementaryPair b)) ∧
       Gadget.Realizes ({⟨4,h⟩} : SignatureFamily AlgebraicComplex) .disequality
         (twoCopyNative h (complementaryPair b)))) := by
  refine ⟨plane_cross_ratio h b ha hs,?_⟩
  rcases plane_cross_relation h b ha hs with hpos | hneg
  · exact Or.inl (plane_positive_factor h b hs hpos)
  · exact Or.inr (plane_negative_exit h b hs hneg)

end
end Holant.Certificates.AffineReference
