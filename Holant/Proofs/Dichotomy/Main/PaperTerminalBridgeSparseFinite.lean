import Holant.Proofs.Dichotomy.Main.PaperTerminalBridgeSparseNormalize
import Holant.Proofs.Dichotomy.Main.PaperTerminalBridgeSparseCanonical
import Holant.Proofs.Dichotomy.Main.PaperTerminalBridgeSparseOrderTwoDeck

/-! A complete actual finite antidiagonal deck normalizes every nonempty
sparse middle support to a genuinely realized complementary q4. The same
original family supplies all phases; no classifier or gate callback is used. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperTerminalBridgeSparseFinite
open Holant Holant.LocalDrafts.Hardness.EightVertexNonexception
namespace C
export PaperTerminalBridgeSparseCanonical (SomeZero Canonical Rigid)
end C
namespace O
export PaperTerminalBridgeSparseNormalize (Output one_pair two_pair)
end O
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option Elab.async false
variable {K : Type} [Field K] [NumberField K]

theorem reindex_first (f : Signature K 4) (e : Equiv.Perm (Fin 4)) :
    (entries (Tensor.reindex e f)).a=(entries f).a := by
  have zero : (![false,false,false,false] : Fin 4→Bool)=(fun _=>false) := by funext i;fin_cases i <;> rfl
  simp only [entries,Tensor.reindex,zero]

theorem reindex_last (f : Signature K 4) (e : Equiv.Perm (Fin 4)) :
    (entries (Tensor.reindex e f)).x=(entries f).x := by
  have one : (![true,true,true,true] : Fin 4→Bool)=(fun _=>true) := by funext i;fin_cases i <;> rfl
  simp only [entries,Tensor.reindex,one]

theorem source (F : SignatureFamily K) (phi : K→+*ℂ) (f : Signature K 4)
    (actual : Gadget.Realizes F .disequality f) (even : EvenSupport f)
    (first : (entries f).a≠0) (last : (entries f).x≠0)
    (live : PaperTerminalBridgeSparseOrders.MiddleLive f) (zero : C.SomeZero (entries f))
    (safe : PaperTerminalBridgeFiniteDeck.NoOneSided F)
    (torsion : ∀t : K,PaperTerminalBridgeAntiGroup.Available F t→t≠0→IsOfFinOrder t) : O.Output F := by
  obtain ⟨m,positive,complex,original⟩:=PaperTerminalBridgeSparseOrderTwoDeck.source F phi f actual even safe torsion
  by_cases one : m=1
  · subst m
    have samples : PaperTerminalBridgeFiniteCaps.Samples 1 (entries f) := by
      simpa [Tensor.reindex] using original (Equiv.refl _)
    obtain ⟨b,c,d⟩:=PaperTerminalBridgeFiniteCaps.order_one _ samples
    apply PaperTerminalBridgeSparseSign.source F f actual even first last live 1 (by simp)
    all_goals simpa only [one_mul]
  by_cases two : m=2
  · subst m
    obtain ⟨ε,square,b,c,d⟩:=PaperTerminalBridgeSparseOrderTwo.source f original
    exact PaperTerminalBridgeSparseSign.source F f actual even first last live ε square b c d
  · have large : 3≤m := by omega
    have rigid : C.Rigid (entries f):=PaperTerminalBridgeSparseLargeOrder.mapped phi large f complex
    obtain ⟨e,hb,hy,hc,hz,rest⟩:=PaperTerminalBridgeSparseCanonical.source f rigid zero live
    let g:=Tensor.reindex e f
    have actual' : Gadget.Realizes F .disequality g := by
      have h:=Holant.Dihedral.CompatibleClosure.realizes_reindex F .disequality f actual e.symm
      simpa only [Equiv.symm_symm] using h
    have even':=PaperTerminalBridgeSparseOrderTwoDeck.even_reindex f even e
    have first' : (entries g).a≠0 := by rw [reindex_first];exact first
    have last' : (entries g).x≠0 := by rw [reindex_last];exact last
    rcases rest with ⟨hd,hw⟩|⟨hd,hw,product⟩
    · exact O.one_pair F g actual' even' first' last' hb hy hc hz hd hw
    · exact O.two_pair F g actual' even' first' last' hb hy hc hz hd hw product

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperTerminalBridgeSparseFinite
end
