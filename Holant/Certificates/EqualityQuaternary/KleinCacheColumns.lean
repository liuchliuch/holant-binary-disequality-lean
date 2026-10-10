import Holant.Certificates.EqualityQuaternary.KleinChecks.Standard00
import Holant.Certificates.EqualityQuaternary.KleinChecks.Standard07
import Holant.Certificates.EqualityQuaternary.KleinChecks.Standard16
import Holant.Certificates.EqualityQuaternary.KleinChecks.Standard23
import Holant.Certificates.EqualityQuaternary.KleinChecks.Exotic00
import Holant.Certificates.EqualityQuaternary.KleinChecks.Exotic07
import Holant.Certificates.EqualityQuaternary.KleinChecks.Exotic16
import Holant.Certificates.EqualityQuaternary.KleinChecks.Exotic23

/-! Each matrix column depends on one actual ordered Bell-label pair. Four
translation permutations contain all sixteen pairs, so their already checked
definition-level columns suffice for every permutation. Remaining checks are
exact equality of cached columns, with no repeated contraction computation.
-/
namespace Holant.Certificates.EqualityQuaternary.Klein.Finite
open Linear
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def translationIndex : Fin 4 → Fin 24 := ![0,7,16,23]
def xorIndex : Fin 4 → Fin 4 → Fin 4 := ![![0,1,2,3],![1,0,3,2],![2,3,0,1],![3,2,1,0]]
def columnTag (p : Fin 24) (a : Fin 4) : Fin 4 := xorIndex a (permutationData p a)

theorem columnTag_correct : ∀ p a,
    permutationData (translationIndex (columnTag p a)) a=permutationData p a := by decide +kernel

theorem translation_cards_correct (kind : Kind) (t : Fin 4) : ∀ ctx out a,
    cards kind (translationIndex t) ctx out a=cardFormula kind (translationIndex t) ctx out a := by
  cases kind <;> fin_cases t
  · exact standardCardsCorrect00
  · exact standardCardsCorrect07
  · exact standardCardsCorrect16
  · exact standardCardsCorrect23
  · exact exoticCardsCorrect00
  · exact exoticCardsCorrect07
  · exact exoticCardsCorrect16
  · exact exoticCardsCorrect23

theorem translation_targets_correct (kind : Kind) (t : Fin 4) : ∀ j,
    targets kind (translationIndex t) j=List.ofFn (targetFormula kind (translationIndex t) j) := by
  cases kind <;> fin_cases t
  · exact standardTargetsCorrect00
  · exact standardTargetsCorrect07
  · exact standardTargetsCorrect16
  · exact standardTargetsCorrect23
  · exact exoticTargetsCorrect00
  · exact exoticTargetsCorrect07
  · exact exoticTargetsCorrect16
  · exact exoticTargetsCorrect23

theorem cards_of_column_reindex (kind : Kind) (p : Fin 24)
    (h : ∀ ctx out a,cards kind p ctx out a=cards kind (translationIndex (columnTag p a)) ctx out a) :
    ∀ ctx out a,cards kind p ctx out a=cardFormula kind p ctx out a := by
  intro ctx out a
  rw [h,translation_cards_correct]
  unfold cardFormula
  rw [columnTag_correct]

theorem targets_length : ∀ kind p j,(targets kind p j).length=16 := by
  intro kind
  cases kind <;> decide +kernel

theorem targetFormula_column (kind : Kind) (p : Fin 24) (j : Fin (planeCount kind)) (col : Fin 16) (a : Fin 4) :
    targetFormula kind (translationIndex (columnTag p a)) j col a=targetFormula kind p j col a := by
  simp only [targetFormula,delta,columnTag_correct]

theorem targets_of_column_reindex (kind : Kind) (p : Fin 24)
    (h : ∀ j (col : Fin 16) a,(targets kind p j).getD col.val (fun _ => 0) a=
      (targets kind (translationIndex (columnTag p a)) j).getD col.val (fun _ => 0) a) :
    ∀ j,targets kind p j=List.ofFn (targetFormula kind p j) := by
  intro j
  apply List.ext_getElem
  · rw [targets_length,List.length_ofFn]
  · intro n hn hn'
    funext a
    have hn16 : n<16 := by simpa only [targets_length] using hn
    have hh := h j ⟨n,hn16⟩ a
    rw [translation_targets_correct,List.getD_eq_getElem _ _ hn] at hh
    rw [List.getD_eq_getElem _ _ (by simp [hn16]),List.getElem_ofFn,targetFormula_column] at hh
    simpa only [List.getElem_ofFn] using hh

end Holant.Certificates.EqualityQuaternary.Klein.Finite
