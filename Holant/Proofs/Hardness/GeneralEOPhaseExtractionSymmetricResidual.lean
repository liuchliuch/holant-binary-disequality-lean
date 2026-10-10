import Holant.Proofs.Hardness.GeneralEOPhaseExtractionLoopTomography

/-! The binary-symmetric residual is genuinely selfdual at every arity.
Every tested binary is an actual native-X graph with exact original labels.
The contrapositive produces an actual asymmetric binary graph from any
non-selfdual central graph. Symmetry alone does not imply ARS. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseExtractionSymmetricResidual
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
namespace E
export GeneralEOCentralHoleCoordinates (reboundary_central)
end E
namespace LN
export LabelledNetwork (Exact)
end LN
set_option backward.isDefEq.respectTransparency false
variable {s : ℕ} {arity : ℕ → ℕ}
variable (G : (i : Fin s) → Signature ℂ (arity i.val))

def BinarySymmetry : Prop :=
  ∀ (B : Network ℂ 2) (BL : Labelling B.shape s 1 arity),
    LN.Exact G B BL → (∀e,B.edge e=Signature.disequality) →
      B.denote ![false,true]=B.denote ![true,false]

theorem binary_selfdual (B : Network ℂ 2) (hE : Signature.CentralSupport B.denote)
    (hB : B.denote ![false,true]=B.denote ![true,false]) : F.SelfDual B.denote := by
  have h00 : B.denote ![false,false]=0 := hE _ (by decide)
  have h11 : B.denote ![true,true]=0 := hE _ (by decide)
  have words (x : Fin 2 → Bool) : x=![x 0,x 1] := by
    funext i
    fin_cases i <;> rfl
  have flipvec (u v : Bool) : F.flip (![u,v] : Fin 2 → Bool)=![!u,!v] := by
    funext i
    fin_cases i <;> rfl
  intro x
  rw [words x,flipvec]
  cases x 0 <;> cases x 1 <;> simp [h00,h11,hB]

/-- MWX's k=1 residual, with its quantification over realized binary gadgets
made explicit. The arity induction uses only original-labelled native loops. -/
theorem selfdual_of_binarySymmetry (hB : BinarySymmetry G) (n : ℕ) :
    ∀ (S : Network ℂ n) (SL : Labelling S.shape s 1 arity),
      LN.Exact G S SL → (∀e,S.edge e=Signature.disequality) →
      Signature.CentralSupport S.denote → F.SelfDual S.denote := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro S SL hL hN hE
    by_cases hn0 : n=0
    · subst n
      intro x
      congr 1
      funext i
      exact Fin.elim0 i
    by_cases hn1 : n=1
    · subst n
      intro x
      rw [hE (F.flip x) (by omega),
        hE x (by omega)]
    by_cases hn2 : n=2
    · subst n
      exact binary_selfdual S hE (hB S SL hL hN)
    have hn3 : 3≤n := by omega
    obtain ⟨k,rfl⟩ : ∃k,n=k+3 := ⟨n-3,by omega⟩
    apply GeneralEOPhaseExtractionLoopTomography.selfDual_of_native_loops S hE
    intro e
    let U := R.reboundary S e
    let UL := R.reboundaryLabels S SL e
    have hUE : Signature.CentralSupport U.denote := E.reboundary_central S e.symm hE
    exact ih (k+1) (by omega) (D.loop U) (D.labels U UL)
      (D.exact G U UL hL) (D.native U hN) (D.central U hUE)

/-- Either all realized binaries are symmetric and the source is selfdual,
or an actual labelled native-X binary witnesses failure of that residual. -/
theorem selfdual_or_asymmetric_binary {n : ℕ} (S : Network ℂ n)
    (SL : Labelling S.shape s 1 arity) (hL : LN.Exact G S SL)
    (hN : ∀e,S.edge e=Signature.disequality) (hE : Signature.CentralSupport S.denote) :
    F.SelfDual S.denote ∨ ∃ (B : Network ℂ 2) (BL : Labelling B.shape s 1 arity),
      LN.Exact G B BL ∧ (∀e,B.edge e=Signature.disequality) ∧
        B.denote ![false,true]≠B.denote ![true,false] := by
  classical
  by_cases hB : BinarySymmetry G
  · exact Or.inl (selfdual_of_binarySymmetry G hB n S SL hL hN hE)
  · right
    simp only [BinarySymmetry,not_forall] at hB
    obtain ⟨B,BL,h⟩ := hB
    exact ⟨B,BL,h.1,h.2.1,h.2.2⟩

/-- The binary-symmetric residual cannot supply the physical signed cap used
by the conditional phase-extraction chain. Its non-ARS case needs another exit. -/
theorem no_nonzero_signed_binary (hB : BinarySymmetry G)
    (B : Network ℂ 2) (BL : Labelling B.shape s 1 arity)
    (hL : LN.Exact G B BL) (hN : ∀e,B.edge e=Signature.disequality)
    (t : ℂ) (ht : t≠0) : ¬GeneralEOPhaseExtractionNetwork.Signed B t := by
  intro hs
  have he := hB B BL hL hN
  rw [hs.2.1,hs.2.2.1] at he
  have hz : (2 : ℂ)*t=0 := by linear_combination he
  exact ht ((mul_eq_zero.mp hz).resolve_left (by norm_num))

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseExtractionSymmetricResidual
