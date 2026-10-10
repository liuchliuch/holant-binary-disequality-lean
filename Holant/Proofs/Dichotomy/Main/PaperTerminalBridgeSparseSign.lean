import Holant.Proofs.Dichotomy.Main.PaperTerminalBridgeSparsePure
import Holant.Proofs.Dichotomy.Main.PaperTerminalBridgeComplementSign
import Holant.Proofs.Dichotomy.Main.PaperTerminalBridgeEqualProductsMiddle

/-! A common negative complementary sign is removed by an actual native
antidiagonal, even when middle entries vanish. A literal permutation moves
one live middle coefficient into the proved cap construction. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperTerminalBridgeSparseSign
open Holant Holant.OpenNetworkComposition
open Holant.LocalDrafts.Hardness.EightVertexNonexception
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
namespace S
export PaperTerminalBridgeComplementSign (Complement signed signed_actual signed_even signed_complement)
end S
namespace O
export PaperTerminalBridgeDenseOrders (reordered order entries_reordered even_reordered)
end O
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option Elab.async false
variable {K : Type} [Field K] [CharZero K]

theorem entries_swap (f : Signature K 4) :
    entries (Tensor.reindex (Equiv.swap (2 : Fin 4) 3) f)=
      ⟨(entries f).a,(entries f).b,(entries f).d,(entries f).c,
        (entries f).z,(entries f).w,(entries f).y,(entries f).x⟩ := by
  apply Entries.ext
  all_goals apply congrArg f
  all_goals funext i;fin_cases i <;> rfl

theorem minus_available (F : SignatureFamily K) (f : Signature K 4)
    (actual : Gadget.Realizes F .disequality f) (even : EvenSupport f)
    (live : PaperTerminalBridgeSparseOrders.MiddleLive f)
    (b : (entries f).b= -(entries f).y) (c : (entries f).c= -(entries f).z)
    (d : (entries f).d= -(entries f).w) : PaperTerminalBridgeAntiGroup.Available F (-1) := by
  have some : (entries f).b≠0 ∨ (entries f).c≠0 ∨ (entries f).d≠0 := by
    rcases live with hb|hc|hd|hw|hz|hy
    · exact Or.inl hb
    · exact Or.inr (Or.inl hc)
    · exact Or.inr (Or.inr hd)
    · exact Or.inr (Or.inr (by rw [d];exact neg_ne_zero.mpr hw))
    · exact Or.inr (Or.inl (by rw [c];exact neg_ne_zero.mpr hz))
    · exact Or.inl (by rw [b];exact neg_ne_zero.mpr hy)
  rcases some with hb|hc|hd
  · have act:=Holant.Dihedral.CompatibleClosure.realizes_reindex F .disequality f actual (O.order 1).symm
    simp only [Equiv.symm_symm] at act
    apply PaperTerminalBridgeComplementSign.minus_available F (O.reordered f 1) act (O.even_reordered f even 1)
    · rw [O.entries_reordered];exact hb
    · rw [O.entries_reordered];exact b
    · rw [O.entries_reordered];exact d
  · exact PaperTerminalBridgeComplementSign.minus_available F f actual even hc c d
  · let e:=Equiv.swap (2 : Fin 4) 3
    have act:=Holant.Dihedral.CompatibleClosure.realizes_reindex F .disequality f actual e.symm
    simp only [Equiv.symm_symm] at act
    apply PaperTerminalBridgeComplementSign.minus_available F (Tensor.reindex e f) act
      (PaperTerminalBridgeEqualProductsMiddle.reindex_even f even e)
    · rw [show e=Equiv.swap (2 : Fin 4) 3 from rfl,entries_swap];exact hd
    · rw [show e=Equiv.swap (2 : Fin 4) 3 from rfl,entries_swap];exact d
    · rw [show e=Equiv.swap (2 : Fin 4) 3 from rfl,entries_swap];exact c

theorem source (F : SignatureFamily K) (f : Signature K 4)
    (actual : Gadget.Realizes F .disequality f) (even : EvenSupport f)
    (first : (entries f).a≠0) (last : (entries f).x≠0)
    (live : PaperTerminalBridgeSparseOrders.MiddleLive f)
    (ε : K) (square : ε^2=1)
    (b : (entries f).b=ε*(entries f).y) (c : (entries f).c=ε*(entries f).z)
    (d : (entries f).d=ε*(entries f).w) :
    ∃g : Signature K 4,Gadget.RealizesUpTo F .disequality g ∧ EvenSupport g ∧
      (entries g).a≠0 ∧ (entries g).x≠0 ∧ S.Complement g := by
  rcases sq_eq_one_iff.mp square with rfl|rfl
  · refine ⟨f,⟨1,one_ne_zero,?_⟩,even,first,last,?_⟩
    · simpa only [one_mul] using actual
    · simpa only [S.Complement,one_mul] using And.intro b (And.intro c d)
  · simp only [neg_mul,one_mul] at b c d
    have phase:=minus_available F f actual even live b c d
    refine ⟨S.signed f,S.signed_actual F f actual phase,S.signed_even f even,?_,?_,S.signed_complement f b c d⟩
    · simpa [entries,S.signed] using first
    · simpa [entries,S.signed] using last

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperTerminalBridgeSparseSign
end
