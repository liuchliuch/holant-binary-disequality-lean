import Holant.Proofs.Hardness.GeneralEOPhaseExtractionSymmetricResidual
import Holant.Proofs.Hardness.GeneralEOSkewPhaseExtraction

/-! Preserve central support in asymmetric-binary extraction. The witness is
obtained by native descent from the selected source, not by quantifying over
possibly noncentral unrelated original-family graphs. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOGeneralPhaseExtraction
open Holant Holant.Complexity FixedGadgetSubstitution
namespace F
export SelfDualPinObstruction (flip SelfDual)
end F
namespace R
export GeneralEOPinnedDescentNetwork (reboundary reboundaryLabels)
end R
namespace D
export GeneralEOPhaseExtractionDistance (loop labels exact native central)
end D
namespace B
export GeneralEOPhaseExtractionFieldBridge (family map_exact map_native map_central
  rebuild labels rebuild_exact rebuild_native rebuild_central map_rebuild)
end B
set_option backward.isDefEq.respectTransparency false
variable {n s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature ℂ (a i.val))

/-- A central asymmetric binary exists whenever the selected central source
is not selfdual, using original labels and native loops throughout. -/
theorem asymmetric_binary (n : ℕ) :
    ∀ (S : Network ℂ n) (SL : Labelling S.shape s 1 a),
      LabelledNetwork.Exact G S SL → (∀e,S.edge e=Signature.disequality) →
      Signature.CentralSupport S.denote → ¬F.SelfDual S.denote →
      ∃ (Q : Network ℂ 2) (QL : Labelling Q.shape s 1 a),
        LabelledNetwork.Exact G Q QL ∧ (∀e,Q.edge e=Signature.disequality) ∧
        Signature.CentralSupport Q.denote ∧ Q.denote ![false,true]≠Q.denote ![true,false] := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro S SL hL hN hE hS
    by_cases hn0 : n=0
    · subst n
      apply (hS ?_).elim
      intro x
      congr 1
      funext i
      exact Fin.elim0 i
    by_cases hn1 : n=1
    · subst n
      apply (hS ?_).elim
      intro x
      rw [hE (F.flip x) (by omega),hE x (by omega)]
    by_cases hn2 : n=2
    · subst n
      exact ⟨S,SL,hL,hN,hE,fun he => hS
        (GeneralEOPhaseExtractionSymmetricResidual.binary_selfdual S hE he)⟩
    obtain ⟨k,rfl⟩ : ∃k,n=k+3 := ⟨n-3,by omega⟩
    have he : ∃e : Equiv.Perm (Fin (k+3)),
        ¬F.SelfDual (D.loop (R.reboundary S e)).denote := by
      by_contra hh
      push Not at hh
      exact hS (GeneralEOPhaseExtractionLoopTomography.selfDual_of_native_loops S hE hh)
    obtain ⟨e,he⟩ := he
    let U := R.reboundary S e
    let UL := R.reboundaryLabels S SL e
    have hUE : Signature.CentralSupport U.denote :=
      GeneralEOCentralHoleCoordinates.reboundary_central S e.symm hE
    exact ih (k+1) (by omega) (D.loop U) (D.labels U UL)
      (D.exact G U UL hL) (D.native U hN) (D.central U hUE) he

variable {K : Type*} [Field K]
variable (H : (i : Fin s)→Signature K (a i.val)) (φ : K→+*ℂ)

/-- Native descent returns the actual graph in the original coefficient field. -/
theorem original_asymmetric_binary (S : Network K n) (SL : Labelling S.shape s 1 a)
    (hL : LabelledNetwork.Exact H S SL) (hN : ∀e,S.edge e=Signature.disequality)
    (hE : Signature.CentralSupport S.denote) (hS : ¬F.SelfDual (S.map φ).denote) :
    ∃ (Q : Network K 2) (QL : Labelling Q.shape s 1 a),
      LabelledNetwork.Exact H Q QL ∧ (∀e,Q.edge e=Signature.disequality) ∧
      Signature.CentralSupport Q.denote ∧ Q.denote ![false,true]≠Q.denote ![true,false] := by
  obtain ⟨Q,QL,hQL,hQN,hQE,hQ⟩ := asymmetric_binary (B.family H φ) n
    (S.map φ) SL (B.map_exact H φ S SL hL) (B.map_native φ S hN)
    (B.map_central φ S hE) hS
  refine ⟨B.rebuild H Q QL,B.labels H Q QL,B.rebuild_exact H Q QL,
    B.rebuild_native H Q QL,B.rebuild_central H φ Q QL hQL hQN hQE,?_⟩
  intro he
  apply hQ
  have he' := congrArg φ he
  rw [←Network.denote_map φ,←Network.denote_map φ,B.map_rebuild H φ Q QL hQL hQN] at he'
  exact he'

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOGeneralPhaseExtraction
