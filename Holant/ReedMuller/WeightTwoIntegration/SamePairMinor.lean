import Holant.ReedMuller.WeightTwoIntegration.SamePairSupport
import Holant.ReedMuller.WeightTwoIntegration.WeightedMinor

/-! The same-original-edge card's literal two-logical-coordinate determinant
vanishes, including its zero-card branch. -/
noncomputable section
namespace Holant.ReedMuller.WeightTwoIntegration
open Holant Holant.ReedMuller.ZeroCardGraph Holant.ReedMuller.MatchingConsistency
variable {K : Type*} [Field K] {n : ℕ} {f : Signature K n}
set_option backward.isDefEq.respectTransparency false

 def logicalBase {r : ℕ} (j k : Fin r) (a b : Bool) : Fin r → Bool :=
  fun d=>if d=j then a else if d=k then b else false

 def logicalPairNumerator {r : ℕ} (h : Signature K r) (i j k : Fin r) (minus a b : Bool) : K :=
  h (Function.update (logicalBase j k a b) i false)+
    (if minus then -1 else 1)*h (Function.update (logicalBase j k a b) i true)

 theorem OriginalPairing.same_pair_lift (C : OriginalPairing f) (i : Fin C.count)
    (t : Fin C.count → Bool) (b : Bool) :
    sameLift (C.ports (i,false)) (C.ports (i,true)) b
      (fun p=>pairedWord C.ports t p.val)=pairedWord C.ports (Function.update t i b) := by
  funext p
  obtain ⟨⟨e,z⟩,rfl⟩ := C.ports.surjective p
  rw [pairedWord_port]
  by_cases he : e=i
  · subst e
    cases z
    · rw [sameLift_left]; simp
    · rw [sameLift_right]; simp
  · have hu : C.ports (e,z)≠C.ports (i,false) := fun h=>he (congrArg Prod.fst (C.ports.injective h))
    have hv : C.ports (e,z)≠C.ports (i,true) := fun h=>he (congrArg Prod.fst (C.ports.injective h))
    rw [sameLift_remaining _ _ _ _ ⟨C.ports (e,z),hu,hv⟩,pairedWord_port,Function.update_of_ne he]

 theorem OriginalPairing.same_pair_card_value (C : OriginalPairing f) (i j k : Fin C.count)
    (minus a b : Bool) :
    card f (C.ports (i,false)) (C.ports (i,true)) minus
      (fun p=>pairedWord C.ports (logicalBase j k a b) p.val)=
      2*logicalPairNumerator C.logical i j k minus a b := by
  simp only [card,C.same_pair_lift,logicalPairNumerator,OriginalPairing.logical]

 theorem OriginalPairing.same_pair_logical_minor (C : OriginalPairing f) (htwo : (2:K)≠0)
    (hd : EqualityDeck f) (hw : WeightedDeck f) (hn : 6≤n) (i j k : Fin C.count) (minus : Bool) :
    logicalPairNumerator C.logical i j k minus false false*logicalPairNumerator C.logical i j k minus true true-
      logicalPairNumerator C.logical i j k minus false true*logicalPairNumerator C.logical i j k minus true false=0 := by
  let y : Bool → Bool → Remaining (C.ports (i,false)) (C.ports (i,true)) → Bool := fun a b p=>pairedWord C.ports (logicalBase j k a b) p.val
  have huv := (C.port_edge i).1
  have hminor :
      card f (C.ports (i,false)) (C.ports (i,true)) minus (y false false)*
        card f (C.ports (i,false)) (C.ports (i,true)) minus (y true true)-
      card f (C.ports (i,false)) (C.ports (i,true)) minus (y false true)*
        card f (C.ports (i,false)) (C.ports (i,true)) minus (y true false)=0 := by
    rcases hw (C.ports (i,false)) (C.ports (i,true)) huv minus with hz | ⟨P,hP⟩
    · rw [hz]
      simp
    · rw [hP]
      apply P.separable_minor y
      · intro a b
        exact C.same_pair_boundary_nonzero htwo hd hn i minus P hP _
          (pairing_support_pairedWord C.matching (logicalBase j k a b))
      · intro p
        by_cases hp : (C.ports.symm p.val).1=j
        · left
          intro a b
          simp [y,pairedWord,logicalBase,hp]
        · right
          intro a b
          simp [y,pairedWord,logicalBase,hp]
  change _=0 at hminor
  simp only [y,C.same_pair_card_value] at hminor
  have hfour : (4:K)≠0 := by convert mul_ne_zero htwo htwo using 1 <;> norm_num
  apply (mul_eq_zero.mp (show (4:K)*(logicalPairNumerator C.logical i j k minus false false*
      logicalPairNumerator C.logical i j k minus true true-logicalPairNumerator C.logical i j k minus false true*
        logicalPairNumerator C.logical i j k minus true false)=0 from by linear_combination hminor)).resolve_left hfour

end Holant.ReedMuller.WeightTwoIntegration
