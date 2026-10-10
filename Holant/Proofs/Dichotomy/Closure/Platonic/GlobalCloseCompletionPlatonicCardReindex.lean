import Holant.Platonic.RankDeficientLocalization.DomainSemantics

/-! Reindexing actual nonsingular card presentations preserves and reflects
their matching labels. Nonzero physical localization scales are retained. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionPlatonicCardReindex
open Holant Holant.Certificates.MatchingContractionClosure
open Holant.Pauli.ExoticKlein
open Holant.Platonic.RainbowLocalization
open Holant.Platonic.RankDeficientLocalization
variable {P Q : Type*} [Fintype P] [Fintype Q] [DecidableEq P] [DecidableEq Q]

theorem mate_reindex (M : Presentation ℂ P) (e : P≃Q) (p : P) :
    (presentationMatching (M.reindex e)).mate (e p)=e ((presentationMatching M).mate p) := by
  simp [presentationMatching,Presentation.reindex,Matching.mate]

theorem mate_reindex_ne (M N : Presentation ℂ P) (e : P≃Q)
    (hne : (presentationMatching M).mate≠(presentationMatching N).mate) :
    (presentationMatching (M.reindex e)).mate≠(presentationMatching (N.reindex e)).mate := by
  intro he
  apply hne
  ext p
  apply e.injective
  simpa only [mate_reindex] using congrArg (fun f : Equiv.Perm Q => f (e p)) he

def cardOfScaledReindex (M : Presentation ℂ P) (e : P≃Q) (c : ℂ) (hc : c≠0)
    (hm : ∀i,(M.matrix i).det≠0) (hs : M.scalar≠0)
    (F : Tensor ℂ Q) (he : F=c • Tensor.reindex e M.tensor) : NonsingularCard F where
  presentation := {M.reindex e with scalar:=c*M.scalar}
  det_ne_zero := hm
  scalar_ne_zero := mul_ne_zero hc hs
  value := by
    rw [he]
    ext x
    simp [Presentation.tensor,Presentation.reindex,productValue,Tensor.reindex,smul_eq_mul,mul_assoc]

theorem scaled_matching_ne (M N : Presentation ℂ P) (e : P≃Q) (c : ℂ) (hc : c≠0)
    (hm : ∀i,(M.matrix i).det≠0) (hn : ∀i,(N.matrix i).det≠0)
    (hs : M.scalar≠0) (ht : N.scalar≠0)
    (F H : Tensor ℂ Q) (he : F=c • Tensor.reindex e M.tensor) (hh : H=c • Tensor.reindex e N.tensor)
    (hne : (presentationMatching M).mate≠(presentationMatching N).mate) :
    (cardOfScaledReindex M e c hc hm hs F he).matching≠
      (cardOfScaledReindex N e c hc hn ht H hh).matching :=
  mate_reindex_ne M N e hne

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionPlatonicCardReindex
end
