import Holant.Proofs.Hardness.GeneralEODEQProducerSupportBasic
import Holant.Proofs.Hardness.GeneralEOARSSupport

/-! Nonpurity on the same common-sign row internally supplies the non-ARS
witness needed by the original-family pin-elimination/hardness split. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEONonpurePinning
open Holant Holant.Tractable
namespace P
export GeneralEODEQProducerSupportBasic (Pure xorList central_charge)
end P
namespace S
export GeneralEOPhaseExtractionSource (inclusion CountingHard)
end S
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
variable {n : ℕ}

theorem closed_xorList (f : Signature AlgebraicComplex n)
    (hc : GeneralEONegativeClosedSupport.Closed f) :
    ∀xs : List (Fin n → Bool), Odd xs.length → (∀x∈xs,f x≠0) → f (P.xorList xs)≠0 := by
  intro xs
  induction xs using List.twoStepInduction with
  | nil => intro ho; simp at ho
  | singleton x =>
    intro _ hs
    simpa [P.xorList] using hs x (by simp)
  | cons_cons x y xs ih _ =>
    intro ho hs
    have ht : Odd xs.length := by
      obtain ⟨k,hk⟩ := ho
      refine ⟨k-1,?_⟩
      simp only [List.length_cons] at hk
      omega
    have hx := hs x (by simp)
    have hy := hs y (by simp)
    have hz := ih ht (fun z h => hs z (by simp [h]))
    have h := hc x y (P.xorList xs) hx hy hz
    have hw : P.xorList (x::y::xs) = tripleXor x y (P.xorList xs) := by
      funext i
      simp only [P.xorList,tripleXor,Bool.xor_assoc]
    rw [hw]
    exact h

theorem closed_pure (f : Signature AlgebraicComplex n)
    (he : Signature.CentralSupport f) (hc : GeneralEONegativeClosedSupport.Closed f)
    (sign : EOSign) : P.Pure sign f := by
  intro xs ho hs
  rw [P.central_charge he (closed_xorList f hc xs ho hs),mul_zero]

theorem nonpure_nonars (f : Signature AlgebraicComplex n) (sign : EOSign)
    (he : Signature.CentralSupport f) (hs : EONegativeWitness.Supports sign ⟨n,f⟩)
    (hp : ¬P.Pure sign f) :
    ¬GeneralEOARSBoundary.ARSUpToScale (fun x => S.inclusion (f x)) := by
  intro ha
  exact hp (closed_pure f he ((GeneralEOARSSupport.ars_supports_iff_closed f ha sign).mp hs) sign)

variable {s : ℕ} {arity : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (arity i.val))

theorem pinning_or_hardness (j : Fin s) (sign : EOSign)
    (he : Signature.CentralSupport (G j))
    (hs : EONegativeWitness.Supports sign ⟨arity j.val,G j⟩)
    (hp : ¬P.Pure sign (G j)) :
    Nonempty (GeneralEOPinEliminationCases.Elimination G) ∨ S.CountingHard G :=
  GeneralEORootNormSource.selected_pinning_or_hardness G j he
    (nonpure_nonars (G j) sign he hs hp)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEONonpurePinning
