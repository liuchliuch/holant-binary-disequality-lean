import Holant.Proofs.Hardness.GeneralEOPhaseExtractionCoordinates
import Holant.Proofs.Hardness.GeneralEOPhaseExtractionReach

/-! Conditional arbitrary-arity phase extraction, with nested well-founded
inductions and a finite trace of actual labelled native-X constructions. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseExtractionInduction
open Holant Holant.Complexity FixedGadgetSubstitution
namespace C
export GeneralEOPhaseExtractionCore (Collinear noncollinear_nonzero)
end C
namespace P
export GeneralEOPhaseExtractionCoordinates (opposite_prefix common_prefix tail3 distance_comp)
end P
namespace E
export GeneralEOCentralHoleCoordinates (tail2 reboundary_word reboundary_central)
end E
namespace R
export GeneralEOPinnedDescentNetwork (reboundary reboundaryLabels)
end R
namespace O
export GeneralEOPinnedDescentOperations (word)
end O
namespace S
export GeneralEOPhaseExtractionStep (network labels exact native central exists_noncollinear)
end S
namespace D
export GeneralEOPhaseExtractionDistance (distance distance_word distance_self
  closer_or_lower loop labels exact native central)
end D
namespace N
export GeneralEOPhaseExtractionNetwork (Signed)
end N
namespace LN
export LabelledNetwork (Exact)
end LN
namespace H
export GeneralEOPhaseExtractionReach (Reach preserves_sign)
end H
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {s : ℕ} {arity : ℕ → ℕ}
variable (G : (i : Fin s) → Signature ℂ (arity i.val))

def Phase {n : ℕ} (f : Signature ℂ n) : Prop := ∃x y,¬C.Collinear (f x) (f y)

def Smaller (B : Network ℂ 2) {n : ℕ} (T : Network ℂ n) : Prop :=
  ∃m,m<n ∧ ∃ (U : Network ℂ m) (UL : Labelling U.shape s 1 arity),
    LN.Exact G U UL ∧ (∀e,U.edge e=Signature.disequality) ∧
    Signature.CentralSupport U.denote ∧ Phase U.denote ∧ H.Reach B T U

def SmallPhase (B : Network ℂ 2) {n : ℕ} (T : Network ℂ n) : Prop :=
  (∃ (U : Network ℂ 2) (UL : Labelling U.shape s 1 arity),
    LN.Exact G U UL ∧ (∀e,U.edge e=Signature.disequality) ∧
    Signature.CentralSupport U.denote ∧ Phase U.denote ∧ H.Reach B T U) ∨
  (∃ (U : Network ℂ 4) (UL : Labelling U.shape s 1 arity),
    LN.Exact G U UL ∧ (∀e,U.edge e=Signature.disequality) ∧
    Signature.CentralSupport U.denote ∧ Phase U.denote ∧ H.Reach B T U)

theorem smaller_prepend (B : Network ℂ 2) {n : ℕ} {T U : Network ℂ n}
    (h : H.Reach B T U) (hU : Smaller G B U) : Smaller G B T := by
  obtain ⟨m,hm,V,VL,hL,hN,hE,hP,hV⟩ := hU
  exact ⟨m,hm,V,VL,hL,hN,hE,hP,_root_.Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseExtractionReach.Reach.trans h hV⟩

theorem smallPhase_prepend (B : Network ℂ 2) {n m : ℕ} {T : Network ℂ n} {U : Network ℂ m}
    (h : H.Reach B T U) (hU : SmallPhase G B U) : SmallPhase G B T := by
  rcases hU with ⟨V,VL,hL,hN,hE,hP,hV⟩|⟨V,VL,hL,hN,hE,hP,hV⟩
  · exact Or.inl ⟨V,VL,hL,hN,hE,hP,_root_.Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseExtractionReach.Reach.trans h hV⟩
  · exact Or.inr ⟨V,VL,hL,hN,hE,hP,_root_.Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseExtractionReach.Reach.trans h hV⟩

variable (B : Network ℂ 2) (BL : Labelling B.shape s 1 arity) (t : ℂ)
variable (hBL : LN.Exact G B BL) (hBN : ∀e,B.edge e=Signature.disequality)
variable (ht : t≠0) (hBt : N.Signed B t)

include hBL hBN ht hBt in
theorem lower_distance (n k : ℕ) : ∀ (T : Network ℂ (n+6))
    (TL : Labelling T.shape s 1 arity), LN.Exact G T TL →
    (∀e,T.edge e=Signature.disequality) → Signature.CentralSupport T.denote →
    ∀x y : Fin (n+6) → Bool,D.distance x y=k →
      ¬C.Collinear (T.denote x) (T.denote y) → Smaller G B T := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro T TL hL hN hE x y hxy hP
    obtain ⟨hx,hy⟩ := C.noncollinear_nonzero hP
    have hwx : 2*weight x=n+6 := by
      by_contra h
      exact hx (hE x h)
    have hwy : 2*weight y=n+6 := by
      by_contra h
      exact hy (hE y h)
    by_cases hk : k=2
    · have hd : D.distance x y=2 := hxy.trans hk
      obtain ⟨e,ex,ey⟩ := P.common_prefix (n:=n+3) x y hwx hwy (by omega) hd
      let U := R.reboundary T e.symm
      let UL := R.reboundaryLabels T TL e.symm
      have hUE : Signature.CentralSupport U.denote := E.reboundary_central T e hE
      have hp : ¬C.Collinear
          (U.denote (GeneralEOPhaseExtractionStep.triple false true true (P.tail3 (x ∘ e))))
          (U.denote (GeneralEOPhaseExtractionStep.triple false true true (P.tail3 (y ∘ e)))) := by
        change ¬C.Collinear ((R.reboundary T e.symm).denote _) ((R.reboundary T e.symm).denote _)
        rw [←ex,←ey,E.reboundary_word,E.reboundary_word]
        exact hP
      obtain ⟨p,b,hpb⟩ := S.exists_noncollinear B U t ht hBt _ _ hp
      refine ⟨n+4,by omega,S.network B U p b,S.labels B U BL UL p b,?_,?_,?_,?_,?_⟩
      · exact S.exact G B U BL UL hBL hL p b
      · exact S.native B U hBN hN p b
      · exact S.central B U t hBt hUE p b
      · exact ⟨_,_,hpb⟩
      · exact _root_.Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseExtractionReach.Reach.trans (_root_.Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseExtractionReach.Reach.reindex T e.symm)
          (_root_.Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseExtractionReach.Reach.trans (_root_.Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseExtractionReach.Reach.reindex U (GeneralEOPhaseExtractionStep.perm p))
            (_root_.Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseExtractionReach.Reach.contract _ b))
    · have hne : x≠y := by
        rintro rfl
        exact hP (by simp [C.Collinear,GeneralEOPhaseExtractionCore.area,mul_comm])
      obtain ⟨e,ex,ey⟩ := P.opposite_prefix (n:=n+4) x y (by omega) hne
      let U := R.reboundary T e.symm
      let UL := R.reboundaryLabels T TL e.symm
      let u := E.tail2 (x ∘ e)
      let v := E.tail2 (y ∘ e)
      have hUE : Signature.CentralSupport U.denote := E.reboundary_central T e hE
      have hu : u≠v := by
        intro huv
        have hd := P.distance_comp x y e
        rw [ex,ey,D.distance_word] at hd
        change (if false=true then 0 else 1)+(if true=false then 0 else 1)+D.distance u v=_ at hd
        rw [huv,D.distance_self] at hd
        have : k=2 := by simpa [hxy] using hd.symm
        exact hk this
      have hp : ¬C.Collinear (U.denote (O.word false true u)) (U.denote (O.word true false v)) := by
        change ¬C.Collinear ((R.reboundary T e.symm).denote _) ((R.reboundary T e.symm).denote _)
        rw [←ex,←ey,E.reboundary_word,E.reboundary_word]
        exact hP
      rcases D.closer_or_lower U u v hu hp with hclose | hlow
      · obtain ⟨z,w,hd,hzw⟩ := hclose
        have hbase : D.distance (O.word false true u) (O.word true false v)=k := by
          rw [←ex,←ey,P.distance_comp,hxy]
        rw [hbase] at hd
        exact smaller_prepend G B (_root_.Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseExtractionReach.Reach.reindex T e.symm)
          (ih (D.distance z w) hd U UL hL hN hUE z w rfl hzw)
      · refine ⟨n+4,by omega,D.loop U,D.labels U UL,?_,?_,?_,?_,?_⟩
        · exact D.exact G U UL hL
        · exact D.native U hN
        · exact D.central U hUE
        · exact ⟨u,v,hlow.1⟩
        · exact _root_.Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseExtractionReach.Reach.trans (_root_.Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseExtractionReach.Reach.reindex T e.symm) (_root_.Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseExtractionReach.Reach.contract U false)

include hBL hBN ht hBt in
theorem lower (n : ℕ) (T : Network ℂ (n+6)) (TL : Labelling T.shape s 1 arity)
    (hL : LN.Exact G T TL) (hN : ∀e,T.edge e=Signature.disequality)
    (hE : Signature.CentralSupport T.denote) (hP : Phase T.denote) : Smaller G B T := by
  obtain ⟨x,y,hxy⟩ := hP
  exact lower_distance G B BL t hBL hBN ht hBt n (D.distance x y) T TL hL hN hE x y rfl hxy

include hBL hBN ht hBt in
theorem reduce (n : ℕ) : ∀ (T : Network ℂ n) (TL : Labelling T.shape s 1 arity),
    LN.Exact G T TL → (∀e,T.edge e=Signature.disequality) →
    Signature.CentralSupport T.denote → Phase T.denote → SmallPhase G B T := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro T TL hL hN hE hP
    by_cases hn2 : n=2
    · subst n
      exact Or.inl ⟨T,TL,hL,hN,hE,hP,_root_.Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseExtractionReach.Reach.refl T⟩
    by_cases hn4 : n=4
    · subst n
      exact Or.inr ⟨T,TL,hL,hN,hE,hP,_root_.Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseExtractionReach.Reach.refl T⟩
    obtain ⟨x,y,hxy⟩ := hP
    have hne : x≠y := by
      rintro rfl
      exact hxy (by simp [C.Collinear,GeneralEOPhaseExtractionCore.area,mul_comm])
    have hn0 : n≠0 := by
      rintro rfl
      exact hne (funext (fun i => Fin.elim0 i))
    have hx := (C.noncollinear_nonzero hxy).1
    have hw : 2*weight x=n := by
      by_contra h
      exact hx (hE x h)
    have hn6 : 6≤n := by omega
    obtain ⟨m,rfl⟩ : ∃m,n=m+6 := ⟨n-6,by omega⟩
    obtain ⟨q,hq,U,UL,hUL,hUN,hUE,hUP,hTrace⟩ := lower G B BL t hBL hBN ht hBt m T TL hL hN hE ⟨x,y,hxy⟩
    exact smallPhase_prepend G B hTrace (ih q hq U UL hUL hUN hUE hUP)

include hBL hBN ht hBt in
theorem quaternary {n : ℕ} (T : Network ℂ n) (TL : Labelling T.shape s 1 arity)
    (hL : LN.Exact G T TL) (hN : ∀e,T.edge e=Signature.disequality)
    (hE : Signature.CentralSupport T.denote) (hP : Phase T.denote)
    (hSign : GeneralEOPhaseExtractionSigns.Sign T.denote) :
    ∃ (Q : Network ℂ 4) (QL : Labelling Q.shape s 1 arity),
      LN.Exact G Q QL ∧ (∀e,Q.edge e=Signature.disequality) ∧
      Signature.CentralSupport Q.denote ∧ Phase Q.denote ∧ H.Reach B T Q := by
  rcases reduce G B BL t hBL hBN ht hBt n T TL hL hN hE hP with h|h
  · obtain ⟨U,UL,hUL,hUN,hUE,⟨x,y,hxy⟩,hTrace⟩ := h
    have hSingle := GeneralEOPhaseExtractionSigns.binary_singlePhase U.denote hUE
      (H.preserves_sign B t hBt hTrace hSign)
    exact False.elim (hxy (hSingle x y))
  · exact h

include hBL hBN ht hBt in
theorem nonars_quaternary {n : ℕ} (T : Network ℂ n) (TL : Labelling T.shape s 1 arity)
    (hL : LN.Exact G T TL) (hN : ∀e,T.edge e=Signature.disequality)
    (hE : Signature.CentralSupport T.denote)
    (hSign : GeneralEOPhaseExtractionSigns.Sign T.denote)
    (hA : ¬GeneralEOARSBoundary.ARSUpToScale T.denote) :
    ∃ (Q : Network ℂ 4) (QL : Labelling Q.shape s 1 arity),
      LN.Exact G Q QL ∧ (∀e,Q.edge e=Signature.disequality) ∧
      Signature.CentralSupport Q.denote ∧ Phase Q.denote ∧ H.Reach B T Q :=
  quaternary G B BL t hBL hBN ht hBt T TL hL hN hE
    (GeneralEOPhaseExtractionStructure.nonars_has_phase T.denote hSign hA) hSign

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseExtractionInduction
