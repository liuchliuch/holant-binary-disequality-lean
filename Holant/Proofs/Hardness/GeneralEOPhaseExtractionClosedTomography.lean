import Holant.Proofs.Hardness.GeneralEOPhaseExtractionLoopTomography

/-! Complete native matching closures separate central selfdual tensors.
The closure relation records an actual boundary permutation and native loop
at every step, ending at an actual closed graph. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseExtractionClosedTomography
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
namespace H
export GeneralEOPhaseExtractionLoopTomography (merge merge_denote merge_flip ext_of_merges)
end H
set_option backward.isDefEq.respectTransparency false

inductive NativeClosure : {n : ℕ} → Network ℂ n → Network ℂ 0 → Prop where
  | done (Q : Network ℂ 0) : NativeClosure Q Q
  | step {n : ℕ} (S : Network ℂ (n+2)) (e : Equiv.Perm (Fin (n+2))) {Q : Network ℂ 0}
      (tail : NativeClosure (D.loop (R.reboundary S e)) Q) : NativeClosure S Q

theorem merge_selfdual {n : ℕ} (f : Signature ℂ (n+2)) (hS : F.SelfDual f)
    (e : Equiv.Perm (Fin (n+2))) : F.SelfDual (H.merge f e) := by
  have hh := congrArg (fun g => H.merge g e) (funext hS)
  rw [H.merge_flip] at hh
  exact congrFun hh

/-- Zero on every actual complete matching closure forces a central selfdual
boundary tensor to vanish. Selfduality is needed at the final binary stage. -/
theorem zero_of_closed (n : ℕ) : ∀ (S : Network ℂ n),
    Signature.CentralSupport S.denote → F.SelfDual S.denote →
    (∀Q,NativeClosure S Q → Q.denote Fin.elim0=0) → S.denote=0 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro S hE hS h0
    by_cases hn0 : n=0
    · subst n
      funext x
      have hx : x=Fin.elim0 := by funext i; exact Fin.elim0 i
      rw [hx]
      exact h0 S (.done S)
    by_cases hn1 : n=1
    · subst n
      funext x
      exact hE x (by omega)
    by_cases hn2 : n=2
    · subst n
      let U := D.loop (R.reboundary S (Equiv.refl _))
      have hv := h0 U (.step S (Equiv.refl _) (.done U))
      rw [H.merge_denote] at hv
      change S.denote ![false,true]+S.denote ![true,false]=0 at hv
      have hf : F.flip (![false,true] : Fin 2 → Bool)=![true,false] := by
        funext i
        fin_cases i <;> rfl
      have hs := hS ![false,true]
      rw [hf] at hs
      have h01 : S.denote ![false,true]=0 := by
        have hh : (2 : ℂ)*S.denote ![false,true]=0 := by linear_combination hv-hs
        exact (mul_eq_zero.mp hh).resolve_left (by norm_num)
      have h10 : S.denote ![true,false]=0 := hs.trans h01
      have h00 : S.denote ![false,false]=0 := hE _ (by decide)
      have h11 : S.denote ![true,true]=0 := hE _ (by decide)
      funext x
      have hx : x=![x 0,x 1] := by funext i; fin_cases i <;> rfl
      rw [hx]
      cases x 0 <;> cases x 1 <;> assumption
    have hn3 : 3≤n := by omega
    obtain ⟨k,rfl⟩ : ∃k,n=k+3 := ⟨n-3,by omega⟩
    apply H.ext_of_merges S.denote 0 hE (by intro x _; rfl)
    intro e
    let U := D.loop (R.reboundary S e)
    have hUE : Signature.CentralSupport U.denote :=
      D.central _ (GeneralEOCentralHoleCoordinates.reboundary_central S e.symm hE)
    have hUS : F.SelfDual U.denote := by
      rw [H.merge_denote]
      exact merge_selfdual S.denote hS e
    have hz := ih (k+1) (by omega) U hUE hUS
      (fun Q hQ => h0 Q (.step S e hQ))
    rw [H.merge_denote] at hz
    have hz0 : H.merge (0 : Signature ℂ (k+3)) e=0 := by
      funext x
      simp [GeneralEOPhaseExtractionLoopTomography.merge]
    rw [hz0]
    exact hz

/-- Contrapositive supplier: a nonzero central selfdual graph has an actual
nonzero closed native matching, constructed without extra vertices. -/
theorem exists_nonzero_closed {n : ℕ} (S : Network ℂ n)
    (hE : Signature.CentralSupport S.denote) (hS : F.SelfDual S.denote)
    (hN : S.denote≠0) : ∃Q : Network ℂ 0,NativeClosure S Q ∧ Q.denote Fin.elim0≠0 := by
  classical
  by_contra h
  push Not at h
  exact hN (zero_of_closed n S hE hS h)

variable {s : ℕ} {a : ℕ→ℕ}

/-- Every closure retains the exact original vertex labels and native edges. -/
theorem labelled {n : ℕ} (G : (i : Fin s)→Signature ℂ (a i.val))
    {S : Network ℂ n} {Q : Network ℂ 0} (h : NativeClosure S Q)
    (SL : Labelling S.shape s 1 a) (hL : LabelledNetwork.Exact G S SL)
    (hN : ∀e,S.edge e=Signature.disequality) :
    ∃QL : Labelling Q.shape s 1 a,LabelledNetwork.Exact G Q QL ∧
      (∀e,Q.edge e=Signature.disequality) := by
  induction h with
  | done Q => exact ⟨SL,hL,hN⟩
  | step S e tail ih =>
    exact ih (D.labels _ (R.reboundaryLabels S SL e))
      (D.exact G _ _ hL) (D.native _ hN)

/-- Closing all boundary ports adds exactly n/2 native edges and no vertices. -/
theorem sizes {n : ℕ} {S : Network ℂ n} {Q : Network ℂ 0} (h : NativeClosure S Q) :
    Q.shape.vertices=S.shape.vertices ∧ Q.shape.edges=S.shape.edges+n/2 := by
  induction h with
  | done Q => exact ⟨rfl,by simp⟩
  | @step n S e Q tail ih =>
    obtain ⟨hv,he⟩ := ih
    refine ⟨hv,?_⟩
    change Q.shape.edges=S.shape.edges+1+n/2 at he
    omega


end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseExtractionClosedTomography
