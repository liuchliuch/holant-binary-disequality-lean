import Holant.Proofs.Hardness.GeneralEOCentralHoleCoordinatesLabels
import Holant.Proofs.Hardness.GeneralEOCentralHolePatternsTerminal
import Holant.Proofs.Hardness.GeneralEOCentralHoleSixLabels

/-! Arbitrary-arity central holes descend to actual labelled quaternary
networks. The family explicitly contains a directed paired pin. Strong
induction is on boundary arity, and every recursive step retains graph labels
and native X edges. No free pairing restriction or hardness hypothesis occurs. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOCentralHoleInduction
open Holant Holant.Tractable Holant.Complexity FixedGadgetSubstitution
namespace H
export GeneralEONegativeSupportTensor (CentralHole)
end H
namespace P
export GeneralEOCentralHolePatterns (central_terminal_partition sixFirst sixSecond sixThird sixHole)
end P
namespace C
export GeneralEOCentralHoleCoordinates (reboundary_word reboundary_central)
end C
namespace L
export GeneralEOCentralHoleCoordinatesLabels (Smaller constant_reduce repeated_reduce)
end L
namespace N
export GeneralEOPinnedDescentNetwork (reboundary reboundaryLabels directed01)
end N
namespace S
export GeneralEOCentralHoleSix (alpha beta gamma delta output output_central output_hole)
end S
namespace SL
export GeneralEOCentralHoleSixLabels (labels exact native)
end SL
namespace LN
export LabelledNetwork (Exact)
end LN
set_option backward.isDefEq.respectTransparency false
variable {s : ℕ} {arity : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (arity i.val))

/-- The endpoint is a real original-labelled graph, not a formal restriction. -/
def QuaternaryHole : Prop :=
  ∃ (Q : Network AlgebraicComplex 4) (QL : Labelling Q.shape s 1 arity),
    LN.Exact G Q QL ∧ (∀i,Q.edge i=Signature.disequality) ∧
    Signature.CentralSupport Q.denote ∧ H.CentralHole Q.denote

variable (j : Fin s) (hj : (⟨arity j.val,G j⟩ : AnySignature AlgebraicComplex)=⟨2,N.directed01⟩)

include hj in
theorem reduce (n : ℕ) : ∀ (T : Network AlgebraicComplex n)
    (TL : Labelling T.shape s 1 arity), LN.Exact G T TL →
    (∀i,T.edge i=Signature.disequality) → Signature.CentralSupport T.denote →
    H.CentralHole T.denote → QuaternaryHole G := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro T TL hL hn he hh
    obtain ⟨W,hz,hd⟩ := hh
    rcases P.central_terminal_partition W.first W.second W.third T.denote he
      W.first_supported W.second_supported W.third_supported hz hd with h | h | h | h
    · obtain ⟨h,e,hp⟩ := h
      obtain ⟨m,hm,U,UL,hU,hN,hE,hH⟩ := L.constant_reduce G T TL j hj hL hn he
        W.first W.second W.third W.first_supported W.second_supported W.third_supported hz hd h e hp
      exact ih m hm U UL hU hN hE hH
    · obtain ⟨h,e,hp⟩ := h
      obtain ⟨m,hm,U,UL,hU,hN,hE,hH⟩ := L.repeated_reduce G T TL j hj hL hn he
        W.first W.second W.third W.first_supported W.second_supported W.third_supported hz hd h e hp
      exact ih m hm U UL hU hN hE hH
    · subst n
      exact ⟨T,TL,hL,hn,he,⟨W,hz,hd⟩⟩
    · obtain ⟨e,ha,hb,hc,hδ⟩ := h
      let U := N.reboundary T e.symm
      let UL := N.reboundaryLabels T TL e.symm
      have hE : Signature.CentralSupport U.denote := C.reboundary_central T e he
      have hA : U.denote S.alpha≠0 := by
        change (N.reboundary T e.symm).denote P.sixFirst≠0
        rw [←ha,C.reboundary_word]
        exact W.first_supported
      have hB : U.denote S.beta≠0 := by
        change (N.reboundary T e.symm).denote P.sixSecond≠0
        rw [←hb,C.reboundary_word]
        exact W.second_supported
      have hC : U.denote S.gamma≠0 := by
        change (N.reboundary T e.symm).denote P.sixThird≠0
        rw [←hc,C.reboundary_word]
        exact W.third_supported
      have hZ : U.denote S.delta=0 := by
        change (N.reboundary T e.symm).denote P.sixHole=0
        rw [←hδ,C.reboundary_word]
        exact hz
      refine ⟨S.output U hE hA hB hC,SL.labels G U UL j hj hE hA hB hC,?_,?_,?_,?_⟩
      · exact SL.exact G U UL j hj hE hA hB hC hL
      · exact SL.native U hE hA hB hC hn
      · exact S.output_central U hE hA hB hC
      · exact S.output_hole U hE hA hB hC hZ

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOCentralHoleInduction
