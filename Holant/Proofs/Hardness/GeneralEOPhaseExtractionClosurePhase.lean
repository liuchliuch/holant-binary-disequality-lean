import Holant.Proofs.Hardness.GeneralEOPhaseExtractionClosedTomography
import Holant.Proofs.Hardness.GeneralEOPhaseExtractionStructure

/-! Complete native closures also detect failure of a common real phase.
An additive coefficient transform is used only analytically; the witnesses
returned at the end are actual native closures of the original source. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseExtractionClosurePhase
open Holant
namespace F
export SelfDualPinObstruction (flip SelfDual)
end F
namespace C
export GeneralEOPhaseExtractionCore (area Collinear collinear_trans noncollinear_nonzero)
end C
namespace P
export GeneralEOPhaseExtractionStructure (SinglePhase ars_of_complement_sign nonars_has_phase)
end P
namespace N
export GeneralEOPhaseExtractionClosedTomography
  (NativeClosure zero_of_closed exists_nonzero_closed)
end N
namespace D
export GeneralEOPhaseExtractionDistance (loop)
end D
namespace R
export GeneralEOPinnedDescentNetwork (reboundary)
end R
namespace H
export GeneralEOPhaseExtractionLoopTomography (merge merge_denote)
end H
set_option backward.isDefEq.respectTransparency false

/-- Replay the same actual boundary permutations and native contractions on
another graph whose boundary tensor is an additive transform of the first. -/
theorem transform_trace (φ : ℂ→+ℂ) {n : ℕ} {T : Network ℂ n} {Q : Network ℂ 0}
    (h : N.NativeClosure T Q) : ∀S : Network ℂ n,
      T.denote=(fun x => φ (S.denote x)) →
      ∃P : Network ℂ 0,N.NativeClosure S P ∧ Q.denote Fin.elim0=φ (P.denote Fin.elim0) := by
  induction h with
  | done Q =>
    intro S hS
    exact ⟨S,.done S,congrFun hS Fin.elim0⟩
  | step T e tail ih =>
    intro S hS
    have he : (D.loop (R.reboundary T e)).denote=
        fun x => φ ((D.loop (R.reboundary S e)).denote x) := by
      rw [H.merge_denote,H.merge_denote]
      funext x
      change T.denote _+T.denote _=φ (S.denote _+S.denote _)
      rw [hS,map_add]
    obtain ⟨P,hP,hv⟩ := ih (D.loop (R.reboundary S e)) he
    exact ⟨P,.step S e hP,hv⟩

def defect (c : ℂ) : ℂ→+ℂ where
  toFun z := (C.area c z : ℂ)
  map_zero' := by simp [C.area]
  map_add' z w := by
    apply Complex.ext <;> simp [C.area]
    ring

theorem singlePhase_of_closed_collinear {n : ℕ} (S : Network ℂ n)
    (hE : Signature.CentralSupport S.denote) (hS : F.SelfDual S.denote)
    (c : ℂ) (hc : c≠0)
    (hC : ∀Q,N.NativeClosure S Q → C.Collinear c (Q.denote Fin.elim0)) :
    P.SinglePhase S.denote := by
  let T := Network.corolla (fun x => defect c (S.denote x))
  have hT : T.denote=(fun x => defect c (S.denote x)) := Network.denote_corolla _
  have hTE : Signature.CentralSupport T.denote := by
    intro x hx
    rw [hT]
    change defect c (S.denote x)=0
    rw [hE x hx,map_zero]
  have hTS : F.SelfDual T.denote := by
    intro x
    rw [hT]
    change defect c (S.denote (F.flip x))=defect c (S.denote x)
    rw [hS]
  have hTZ : T.denote=0 := N.zero_of_closed n T hTE hTS (by
    intro Q hQ
    obtain ⟨U,hU,hu⟩ := transform_trace (defect c) hQ S hT
    rw [hu]
    change (C.area c (U.denote Fin.elim0) : ℂ)=0
    rw [show C.area c (U.denote Fin.elim0)=0 from hC U hU]
    rfl)
  have hphase (x : Fin n → Bool) : C.Collinear c (S.denote x) := by
    have hz := congrFun hTZ x
    rw [hT] at hz
    change (C.area c (S.denote x) : ℂ)=0 at hz
    exact Complex.ofReal_eq_zero.mp hz
  intro x y
  have hx : C.Collinear (S.denote x) c := by
    have hh := hphase x
    unfold C.Collinear C.area at hh ⊢
    linarith
  exact C.collinear_trans hc hx (hphase y)

/-- Every central selfdual non-ARS source has two actual complete native
matching closures whose nonzero scalar values have different real phases. -/
theorem nonars_closed_phase {n : ℕ} (S : Network ℂ n)
    (hE : Signature.CentralSupport S.denote) (hS : F.SelfDual S.denote)
    (hA : ¬GeneralEOARSBoundary.ARSUpToScale S.denote) :
    ∃P Q : Network ℂ 0,N.NativeClosure S P ∧ N.NativeClosure S Q ∧
      ¬C.Collinear (P.denote Fin.elim0) (Q.denote Fin.elim0) := by
  classical
  obtain ⟨x,y,hxy⟩ := P.nonars_has_phase S.denote (Or.inl hS) hA
  have hN : S.denote≠0 := by
    intro hz
    exact (C.noncollinear_nonzero hxy).1 (congrFun hz x)
  obtain ⟨U,hU,hu⟩ := N.exists_nonzero_closed S hE hS hN
  by_contra h
  push Not at h
  have hp := singlePhase_of_closed_collinear S hE hS (U.denote Fin.elim0) hu
    (fun Q hQ => h U Q hU hQ)
  exact hA (P.ars_of_complement_sign S.denote hp (Or.inl hS))

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseExtractionClosurePhase
