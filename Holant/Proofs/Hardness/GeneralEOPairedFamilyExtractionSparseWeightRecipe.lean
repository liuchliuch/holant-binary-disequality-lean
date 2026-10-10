import Holant.Proofs.Hardness.GeneralEOPairedFamilyExtractionRecipe
import Holant.Proofs.Hardness.GeneralEOPairedFamilyExtractionSparseWeightBinary

/-! The sparse unequal-fourth branch selects its parity and unary directly
from the input row. At most two actual unary copies and one Boolean trace
produce a hard binary. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionSparseWeightRecipe
open Holant Holant.Tractable
open scoped BigOperators
namespace S
export GeneralEOPairedFamilyExtractionSupport (origin XorClosed MeetClosed exists_parity parityRow)
end S
namespace T
export GeneralEOPairedFamilyExtractionTensor (substitute)
end T
namespace O
export GeneralEOPairedFamilyExtractionOrigin (paritySubstitution parityWord_substitute)
end O
namespace W
export GeneralEOPairedFamilyExtractionWeight (CommonFourthSupport exists_weight)
end W
namespace B
export GeneralEOPairedFamilyExtractionPhaseBundle (evaluate)
end B
namespace R
export GeneralEOPairedFamilyExtractionRecipe (Recipe Bad denote)
end R
namespace H
export GeneralEOPairedFamilyExtractionSparseWeightBinary (binary row exists_hard_binary)
end H
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false

variable {n : ℕ}

def weightPorts (w : Fin n → Bool) : Fin n → Bool ⊕ Fin 3 :=
  fun i=>if w i then Sum.inr 2 else Sum.inl false

theorem weight_value (f : Signature AlgebraicComplex n) (w : Fin n → Bool) (z : Fin 3 → Bool) :
    f (T.substitute (weightPorts w) z)=if z 2 then f w else f S.origin := by
  cases h : z 2 <;> simp only [Bool.false_eq_true,ite_false,ite_true]
  · apply congrArg f
    funext i
    cases hi : w i <;> simp [T.substitute,weightPorts,S.origin,hi,h]
  · apply congrArg f
    funext i
    cases hi : w i <;> simp [T.substitute,weightPorts,hi,h]

theorem parity_trace (q : Signature AlgebraicComplex 3)
    (hq : ∀z,q z≠0 ↔ Bool.xor (Bool.xor (z 0) (z 1)) (z 2)=false)
    (u v : AlgebraicComplex) (e : ℕ) (z : Fin 2 → Bool) :
    (∑b : Bool,q (Fin.snoc z b)*(if b then v else u)^e)=
      H.binary (q ![false,false,false]) (q ![true,true,false])
        (q ![true,false,true]) (q ![false,true,true]) u v e z := by
  have h001 : q ![false,false,true]=0 := by simpa using not_iff_not.mpr (hq ![false,false,true])
  have h010 : q ![false,true,false]=0 := by simpa using not_iff_not.mpr (hq ![false,true,false])
  have h100 : q ![true,false,false]=0 := by simpa using not_iff_not.mpr (hq ![true,false,false])
  have h111 : q ![true,true,true]=0 := by simpa using not_iff_not.mpr (hq ![true,true,true])
  have he (b : Bool) : Fin.snoc z b=![z 0,z 1,b] := by funext i; fin_cases i <;> rfl
  rw [Fintype.sum_bool]
  simp only [he]
  cases hz0 : z 0 <;> cases hz1 : z 1 <;>
    simp [H.binary,H.row,hz0,hz1,h001,h010,h100,h111]

theorem exists_recipe (f : Signature AlgebraicComplex n) (h0 : f S.origin≠0)
    (hx : S.XorClosed f) (hm : ¬S.MeetClosed f) (hw : ¬W.CommonFourthSupport f) :
    ∃r : R.Recipe n,R.Bad f r := by
  obtain ⟨u,v,_,_,hs,_⟩ := S.exists_parity f h0 hx hm
  obtain ⟨w,hw0,hfour,_,_⟩ := W.exists_weight f h0 hw
  let q := S.parityRow f u v
  have hq : ∀z,q z≠0 ↔ Bool.xor (Bool.xor (z 0) (z 1)) (z 2)=false := hs
  have h000 : q ![false,false,false]≠0 := (hq _).mpr (by decide)
  have h110 : q ![true,true,false]≠0 := (hq _).mpr (by decide)
  have h101 : q ![true,false,true]≠0 := (hq _).mpr (by decide)
  have h011 : q ![false,true,true]≠0 := (hq _).mpr (by decide)
  obtain ⟨e,_,_,ha,hp⟩ := H.exists_hard_binary h000 h110 h101 h011 h0 hw0 (Ne.symm hfour)
  let ps := O.paritySubstitution u v::List.replicate e (weightPorts w)
  have he : R.denote f (.marginal ps)=H.binary (q ![false,false,false]) (q ![true,true,false])
      (q ![true,false,true]) (q ![false,true,true]) (f S.origin) (f w) e := by
    funext z
    change (∑b : Bool,B.evaluate f ps (Fin.snoc z b))=_
    simp only [B.evaluate,ps,List.map_cons,List.prod_cons,List.map_replicate,List.prod_replicate]
    have hpar (x : Fin 3 → Bool) : f (T.substitute (O.paritySubstitution u v) x)=q x := by
      rw [←O.parityWord_substitute]
      rfl
    simp_rw [hpar,weight_value]
    exact parity_trace q hq (f S.origin) (f w) e z
  refine ⟨.marginal ps,?_⟩
  unfold R.Bad
  rw [he]
  exact ⟨ha,hp⟩

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionSparseWeightRecipe
