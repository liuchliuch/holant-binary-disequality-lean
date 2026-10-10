import Holant.ReedMuller.SupportReconstruction.Parity

/-! The complete equal-ij support slice is exactly the source parity-lift
linear code. Both directions follow from the actual card equations. -/
noncomputable section
namespace Holant.ReedMuller.SupportReconstruction
open Holant Holant.ReedMuller.ZeroCardGraph Holant.ReedMuller.MatchingConsistency
open Holant.ReedMuller.WeightTwoIntegration Holant.ReedMuller.FlatNetwork Holant.ReedMuller.LowArity
variable {n : ℕ} {i j : Fin n}
set_option backward.isDefEq.respectTransparency false

 theorem word_slice (P : WeightedProduct ℂ (Remaining i j)) (t : BinaryVector P.edges) :
    wordVector (sliceWord P.ports t)=sameLift i j (boolEquiv.symm (∑e,t e))
      (logicalWord P (wordVector t)) := by
  funext k
  by_cases hi : k=i
  · subst k
    change boolEquiv.symm (sliceWord P.ports t i)=_
    rw [sliceWord_left,sameLift_left]
  · by_cases hj : k=j
    · subst k
      change boolEquiv.symm (sliceWord P.ports t j)=_
      rw [sliceWord_right,sameLift_right]
    · simp [wordVector,sliceWord,sameLift,hi,hj,logicalWord]

 theorem MatchingCards.slice_exact {f : Signature ℂ n} (D : MatchingCards f i j)
    (hW : weightGraph f=⊥) (x : BinaryVector n) :
    (f (wordVector x)≠0 ∧ x i=x j) ↔ x∈sliceCode D.plus.ports := by
  constructor
  · rintro ⟨hfx,hij⟩
    let y : Remaining i j → Bool := fun p=>wordVector x p.val
    let b : Bool := wordVector x i
    have hrec : sameLift i j b y=wordVector x := sameLift_reconstruct i j (wordVector x)
      (congrArg boolEquiv.symm hij)
    have hmatch := D.matching_of_lift b y (by rwa [hrec])
    let t : Fin D.plus.edges → Bool := fun e=>y (D.plus.ports (e,false))
    have hlog : logicalWord D.plus t=y := D.logical_reconstruct y hmatch
    have hp := (D.selected_lift hW t b).mp (by rw [hlog,hrec];exact hfx)
    have hxi : x i=∑e,vectorWord t e := by
      simpa only [b,wordVector,Equiv.apply_symm_apply,parity] using hp
    refine ⟨vectorWord t,?_⟩
    funext k
    change sliceWord D.plus.ports (vectorWord t) k=x k
    by_cases hi : k=i
    · subst k; rw [sliceWord_left]; exact hxi.symm
    · by_cases hj : k=j
      · subst k; rw [sliceWord_right]; exact hxi.symm.trans hij
      · have hh := congrFun hlog ⟨k,hi,hj⟩
        have hb := congrArg boolEquiv hh
        simpa only [sliceWord,hi,hj,dite_false,logicalWord,y,wordVector,vectorWord,Equiv.apply_symm_apply] using hb
  · rintro ⟨t,rfl⟩
    constructor
    · change f (wordVector (sliceWord D.plus.ports t))≠0
      rw [word_slice]
      apply (D.selected_lift hW (wordVector t) _).mpr
      simp only [Equiv.apply_symm_apply,parity,vector_word]
    · simp [sliceLinear]

end Holant.ReedMuller.SupportReconstruction
