import Holant.Proofs.Hardness.GeneralEOPureLoopStep
import Holant.Proofs.Hardness.GeneralEOPureOperations

/-! Pure common-sign EO restrictions descend by native self-loops until their
whole affine span is central. Every step preserves the original network labels,
all coefficients, and the selected failed A/P restriction. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPureLoopSource
open Holant Holant.Tractable Holant.Complexity FixedGadgetSubstitution
open GeneralEOPureLoopCore GeneralEODEQProducerSupportBasic
namespace A
export GeneralEOPureAffineSpan (signBit central_or_fixed closed_of_span_central)
end A
namespace S
export GeneralEOPureLoopStep
  (normalized output labels exact native central orientation output_slice bad arity_lt)
end S
namespace P
export GeneralEOPureOperations (slice slice_pure slice_supports reboundary_pure reboundary_supports)
end P
set_option backward.isDefEq.respectTransparency false
variable {s : ℕ} {a : ℕ → ℕ}

/-- Any chosen slot can be brought first without changing its orientation. -/
theorem slot_exists {k : ℕ} (j : Fin k) :
    ∃ m, ∃ e : Fin (m+1) ≃ Fin k, e 0=j := by
  have hk : k≠0 := by have hj := j.isLt; omega
  obtain ⟨m,hm⟩ := Nat.exists_eq_succ_of_ne_zero hk
  let e₀ : Fin (m+1) ≃ Fin k := finCongr hm.symm
  refine ⟨m,(Equiv.swap 0 (e₀.symm j)).trans e₀,?_⟩
  simp

/-- Native forced-pair deletion terminates with closed support and an actual
failed pairing. No pin access, covering pairing, or derived free row is assumed. -/
theorem reduce (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
    (sign : EOSign) (C : EOClass) (n : ℕ)
    (T : Network AlgebraicComplex n) (L : Labelling T.shape s 1 a)
    (hex : LabelledNetwork.Exact G T L) (hnative : ∀e,T.edge e=Signature.disequality)
    (hcentral : Signature.CentralSupport T.denote)
    (hsupport : EONegativeWitness.Supports sign ⟨n,T.denote⟩)
    (hpure : Pure sign T.denote) (p : OrientedPerfectPairing n)
    (hbad : ¬C.Holds (p.restrict T.denote)) : Nonempty (Reduced G C) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hnonzero := nonzero_of_bad T.denote p C hbad
    rcases A.central_or_fixed T.denote hnonzero sign hpure with hspan | ⟨i,hfixed⟩
    · exact ⟨{
        arity := n
        network := T
        labels := L
        exact := hex
        native := hnative
        central := hcentral
        nonzero := hnonzero
        closed := A.closed_of_span_central T.denote sign hsupport hspan
        pairing := p
        bad := hbad }⟩
    · obtain ⟨m,e,he⟩ := slot_exists (p.ports.symm i).1
      let side := (p.ports.symm i).2
      have hf : ∀x,T.denote x≠0 → x (p.ports (e 0,side))=A.signBit sign := by
        intro x hx
        have hi : p.ports (e 0,side)=i := by
          rw [he]
          exact p.ports.apply_symm_apply i
        rw [hi]
        exact hfixed x hx
      have hvalue : (S.output T p e).denote =
          P.slice (S.normalized T p e).denote (S.orientation (A.signBit sign) side) := by
        funext x
        exact S.output_slice T p e (A.signBit sign) side hf x
      have hs : EONegativeWitness.Supports sign ⟨m*2,(S.output T p e).denote⟩ := by
        rw [hvalue]
        apply P.slice_supports
        exact P.reboundary_supports T sign hsupport (normalize p e).symm
      have hp : Pure sign (S.output T p e).denote := by
        rw [hvalue]
        apply P.slice_pure
        exact P.reboundary_pure T sign hpure (normalize p e).symm
      exact ih (m*2) (S.arity_lt p e) (S.output T p e) (S.labels T L p e)
        (S.exact G T L hex p e) (S.native T hnative p e) (S.central T hcentral p e)
        hs hp (standard m) (S.bad T p e (A.signBit sign) side hf C hbad)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPureLoopSource
