import Holant.ReedMuller.WeightTwoIntegration.ThreeLogical
import Holant.ReedMuller.WeightTwoIntegration.SamePairMinor

/-! Exceptional square relations are consequences of actual same-original-edge
card determinants, not hypotheses supplied to the source theorem. -/
noncomputable section
namespace Holant.ReedMuller.WeightTwoIntegration
open Holant Holant.ReedMuller.ZeroCardGraph Holant.ReedMuller.MatchingConsistency
set_option backward.isDefEq.respectTransparency false

 theorem three_word_eta (t : Fin 3 → Bool) : t=![t 0,t 1,t 2] := by
  funext i
  fin_cases i <;> rfl

 theorem logicalPairNumerator_cast {r : ℕ} (e : r=3) (h : Signature ℂ r)
    (i j k : Fin 3) (minus a b : Bool) :
    logicalPairNumerator h (Fin.cast e.symm i) (Fin.cast e.symm j) (Fin.cast e.symm k) minus a b=
      logicalPairNumerator (fun t=>h (fun s=>t (Fin.cast e s))) i j k minus a b := by
  subst r
  rfl

 theorem three_pair_numerator (h : Signature ℂ 3) (rho : Fin 3 → ℂ) (kap c : ℂ)
    (he : ∀a b d,h ![a,b,d]=c*exceptionalH rho kap a b d)
    (i : Fin 3) (minus a b : Bool) :
    logicalPairNumerator h i (exceptionalRemainingLeft i) (exceptionalRemainingRight i) minus a b=
      c*exceptionalSamePairCard rho kap i minus a b := by
  have hall (t : Fin 3 → Bool) : h t=c*exceptionalH rho kap (t 0) (t 1) (t 2) := by
    conv_lhs => rw [three_word_eta t]
    exact he _ _ _
  fin_cases i <;> cases minus <;>
    simp [logicalPairNumerator,hall,logicalBase,exceptionalRemainingLeft,exceptionalRemainingRight,
      exceptionalSamePairCard] <;> ring

 namespace OriginalPairing
 variable {n : ℕ} {f : Signature ℂ n}

 theorem three_square_relations (C : OriginalPairing f) (H : Consistent f)
    (hd : EqualityDeck f) (hw : WeightedDeck f) (hn : 6≤n) (hc : C.count=3)
    (rho : Fin 3 → ℂˣ) (kap : ℂˣ) (hk : (kap:ℂ)≠1)
    (he : ∀a b c,C.threeLogical hc ![a,b,c]=C.logical (fun _=>false)*
      exceptionalH (fun i=>(rho i:ℂ)) kap a b c) :
    ∀i : Fin 3,(kap:ℂ)*(rho i:ℂ)^2=1 := by
  intro i
  have hm := C.same_pair_logical_minor (by norm_num) hd hw hn (Fin.cast hc.symm i)
    (Fin.cast hc.symm (exceptionalRemainingLeft i)) (Fin.cast hc.symm (exceptionalRemainingRight i)) false
  have hval (a b : Bool) :
      logicalPairNumerator C.logical (Fin.cast hc.symm i)
        (Fin.cast hc.symm (exceptionalRemainingLeft i)) (Fin.cast hc.symm (exceptionalRemainingRight i)) false a b=
      C.logical (fun _=>false)*exceptionalSamePairCard (fun j=>(rho j:ℂ)) kap i false a b := by
    rw [logicalPairNumerator_cast]
    exact three_pair_numerator (C.threeLogical hc) (fun j=>(rho j:ℂ)) kap _ he i false a b
  simp only [hval] at hm
  have h0 := C.logical_nonzero (by norm_num) H hd hn (fun _=>false)
  apply exceptional_square_of_samePair_rank_one (fun j=>(rho j:ℂ)) kap (fun j=>(rho j).ne_zero) hk i false
  apply (mul_eq_zero.mp (show C.logical (fun _=>false)^2*
      (exceptionalSamePairCard (fun j=>(rho j:ℂ)) kap i false false false*
        exceptionalSamePairCard (fun j=>(rho j:ℂ)) kap i false true true-
       exceptionalSamePairCard (fun j=>(rho j:ℂ)) kap i false false true*
        exceptionalSamePairCard (fun j=>(rho j:ℂ)) kap i false true false)=0 from by
      linear_combination hm)).resolve_left (pow_ne_zero 2 h0)

 end OriginalPairing
end Holant.ReedMuller.WeightTwoIntegration
