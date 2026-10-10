import Holant.Proofs.Hardness.GeneralEOPhaseExtractionStep
import Holant.Proofs.Hardness.GeneralEOPhaseExtractionStructure

/-! Common complement-sign preservation for every actual phase-descent operation. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseExtractionSigns
open Holant
namespace F
export SelfDualPinObstruction (flip)
end F
namespace N
export GeneralEOPhaseExtractionNetwork (Signed network denote value)
end N
namespace R
export GeneralEOPinnedDescentNetwork (reboundary reboundary_denote)
end R
namespace O
export GeneralEOPinnedDescentOperations (word)
end O
namespace C
export GeneralEOPhaseExtractionCore (Collinear)
end C
set_option backward.isDefEq.respectTransparency false

def Sign {n : ℕ} (f : Signature ℂ n) : Prop :=
  (∀x,f (F.flip x)=f x) ∨ (∀x,f (F.flip x)= -f x)

theorem reboundary {n m : ℕ} (S : Network ℂ n) (e : Fin n ≃ Fin m)
    (hS : Sign S.denote) : Sign (R.reboundary S e).denote := by
  rcases hS with hS|hS
  · left
    intro x
    rw [R.reboundary_denote]
    exact hS (x ∘ e)
  · right
    intro x
    rw [R.reboundary_denote]
    exact hS (x ∘ e)

theorem flip_word {n : ℕ} (u v : Bool) (x : Fin n → Bool) :
    F.flip (O.word u v x)=O.word (!u) (!v) (F.flip x) := by
  funext i
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun _ => ?_) i) i <;> rfl

theorem contraction {n : ℕ} (B : Network ℂ 2) (S : Network ℂ (n+2)) (t : ℂ)
    (hB : N.Signed B t) (hS : Sign S.denote) (minus : Bool) :
    Sign (N.network B S minus).denote := by
  rcases hS with hS|hS
  · cases minus
    · left
      intro x
      have h01 := hS (O.word true false x)
      have h10 := hS (O.word false true x)
      simp only [flip_word,Bool.not_false,Bool.not_true] at h01 h10
      rw [N.denote B S t hB,N.denote B S t hB]
      simp [N.value,h01,h10,add_comm]
    · right
      intro x
      have h01 := hS (O.word true false x)
      have h10 := hS (O.word false true x)
      simp only [flip_word,Bool.not_false,Bool.not_true] at h01 h10
      rw [N.denote B S t hB,N.denote B S t hB]
      simp only [N.value,ite_true,h01,h10]
      ring
  · cases minus
    · right
      intro x
      have h01 := hS (O.word true false x)
      have h10 := hS (O.word false true x)
      simp only [flip_word,Bool.not_false,Bool.not_true] at h01 h10
      rw [N.denote B S t hB,N.denote B S t hB]
      simp only [N.value,Bool.false_eq_true,ite_false,h01,h10]
      ring
    · left
      intro x
      have h01 := hS (O.word true false x)
      have h10 := hS (O.word false true x)
      simp only [flip_word,Bool.not_false,Bool.not_true] at h01 h10
      rw [N.denote B S t hB,N.denote B S t hB]
      simp only [N.value,ite_true,h01,h10]
      ring

theorem step {n : ℕ} (B : Network ℂ 2) (S : Network ℂ (n+3)) (t : ℂ)
    (hB : N.Signed B t) (hS : Sign S.denote)
    (p : GeneralEOPhaseExtractionStep.Pair) (minus : Bool) :
    Sign (GeneralEOPhaseExtractionStep.network B S p minus).denote :=
  contraction B (R.reboundary S (GeneralEOPhaseExtractionStep.perm p)) t hB
    (reboundary S _ hS) minus

theorem binary_singlePhase (f : Signature ℂ 2) (hE : Signature.CentralSupport f)
    (hS : Sign f) : GeneralEOPhaseExtractionStructure.SinglePhase f := by
  have h00 : f ![false,false]=0 := hE _ (by decide)
  have h11 : f ![true,true]=0 := hE _ (by decide)
  have hf : F.flip (![false,true] : Fin 2 → Bool)=![true,false] := by
    funext i
    fin_cases i <;> rfl
  have words (x : Fin 2 → Bool) : x=![x 0,x 1] := by
    funext i
    fin_cases i <;> rfl
  intro x y
  rw [words x,words y]
  rcases hS with hS|hS
  · have h10 := hS ![false,true]
    rw [hf] at h10
    cases x 0 <;> cases x 1 <;> cases y 0 <;> cases y 1 <;>
      simp [h00,h11,h10,C.Collinear,GeneralEOPhaseExtractionCore.area] <;> ring
  · have h10 := hS ![false,true]
    rw [hf] at h10
    cases x 0 <;> cases x 1 <;> cases y 0 <;> cases y 1 <;>
      simp [h00,h11,h10,C.Collinear,GeneralEOPhaseExtractionCore.area] <;> ring

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseExtractionSigns
