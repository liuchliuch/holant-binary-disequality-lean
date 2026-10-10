import Holant.Certificates.AffineReference.FullEvenCoverage
import Holant.EightVertex.ProductAnchor.FactorEquality

/-! Actual affine support-four references, in their original two ordered
blocks. The sign cross-ratio is derived from the affine phase criterion. -/
namespace Holant.Certificates.AffineReference
open Holant Holant.Tractable Holant.Tractable.AffinePhase
noncomputable section
set_option backward.isDefEq.respectTransparency false

 def OnPlane (b : Fin 3) (x : Fin 4 → Bool) : Prop :=
  x (blockPair b).1=x (blockPair b).2 ∧ x (blockComplement b).1=x (blockComplement b).2

 instance (b : Fin 3) (x : Fin 4 → Bool) : Decidable (OnPlane b x) :=
  inferInstanceAs (Decidable (_ ∧ _))

 def PlaneSupport (h : Signature AlgebraicComplex 4) (b : Fin 3) : Prop :=
  ∀ x,h x≠0 ↔ OnPlane b x

 def planeChart (b : Fin 3) (y : Fin 2 → Bool) : Fin 4 → Bool := fun i =>
  if i=(blockPair b).1 ∨ i=(blockPair b).2 then y 0 else y 1

 theorem planeChart_affine : ∀ b,TwoTranslate.IsAffineMap (planeChart b) := by
  unfold TwoTranslate.IsAffineMap
  decide

 theorem planeChart_onPlane : ∀ b y,OnPlane b (planeChart b y) := by decide

 theorem planeChart_original : ∀ b x,OnPlane b x →
    planeChart b ![x (blockPair b).1,x (blockComplement b).1]=x := by decide

 theorem planeChart_zero : ∀ b,planeChart b (fun _ => false)=(fun _ => false) := by decide
 theorem planeChart_one : ∀ b,planeChart b (fun _ => true)=(fun _ => true) := by decide

 def planeTable (h : Signature AlgebraicComplex 4) (b : Fin 3) : Signature AlgebraicComplex 2 :=
  fun y => h (planeChart b y)

 theorem planeTable_nonzero (h : Signature AlgebraicComplex 4) (b : Fin 3)
    (hs : PlaneSupport h b) (y : Fin 2 → Bool) : planeTable h b y≠0 :=
  (hs _).mpr (planeChart_onPlane b y)

 theorem planeTable_affine (h : Signature AlgebraicComplex 4) (b : Fin 3)
    (ha : Affine h) (hs : PlaneSupport h b) : Affine (planeTable h b) := by
  rcases ha with hz | ⟨c,hc,S,Q,hf⟩
  · have hn := planeTable_nonzero h b hs (fun _ => false)
    simp [planeTable,hz] at hn
  have hholds (y : Fin 2 → Bool) : S.Holds (planeChart b y) := by
    have hn := planeTable_nonzero h b hs y
    change h (planeChart b y)≠0 at hn
    rw [hf] at hn
    by_contra hh
    simp [affineFormula,hh] at hn
  have H := (TwoTranslate.affine_quadratic_precompose Q (planeChart b) (planeChart_affine b)).scale c
  convert H using 1
  funext y
  simp [planeTable,hf,affineFormula,hholds y]

 theorem plane_cross_ratio (h : Signature AlgebraicComplex 4) (b : Fin 3)
    (ha : Affine h) (hs : PlaneSupport h b) :
    let f := planeTable h b
    f ![false,false]*f ![true,true]/(f ![false,true]*f ![true,false])=1 ∨
      f ![false,false]*f ![true,true]/(f ![false,true]*f ![true,false])= -1 := by
  have hn := planeTable_nonzero h b hs
  have ht := thirdTrivial_of_affine hn (planeTable_affine h b ha hs)
  have H := secondRatio_sq hn ht (![true,false]) (![false,true])
  have ho : (origin 2 : Fin 2 → Bool)=![false,false] := by decide
  have hx : xor (![true,false] : Fin 2 → Bool) ![false,true]=![true,true] := by decide
  simp only [secondRatio,AffinePhase.origin_xor,hx] at H
  rw [ho] at H
  have He : (planeTable h b ![false,false]*planeTable h b ![true,true]/
      (planeTable h b ![false,true]*planeTable h b ![true,false]))^2=1 := by
    simpa [mul_comm] using H
  exact sq_eq_one_iff.mp He

 theorem plane_cross_relation (h : Signature AlgebraicComplex 4) (b : Fin 3)
    (ha : Affine h) (hs : PlaneSupport h b) :
    let f := planeTable h b
    f ![false,false]*f ![true,true]=f ![false,true]*f ![true,false] ∨
      f ![false,false]*f ![true,true]= -(f ![false,true]*f ![true,false]) := by
  have hn := mul_ne_zero (planeTable_nonzero h b hs ![false,true])
    (planeTable_nonzero h b hs ![true,false])
  rcases plane_cross_ratio h b ha hs with h | h
  · exact Or.inl ((div_eq_one_iff_eq hn).mp h)
  · right
    have H := (div_eq_iff hn).mp h
    simpa using H

end
end Holant.Certificates.AffineReference
