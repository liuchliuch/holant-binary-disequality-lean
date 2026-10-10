import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2SparsePrimeAnchors
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2SignedSixTerminal
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2OrdinaryShape

/-! Canonical prime q4s supply actual Eq4 or close the whole family. The
Affine-row residual is eliminated by genuine sparse anchor graphs and exact
original-field proper-factor exclusions, not by a family-membership assumption. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2CanonicalPrime
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.RemoteWork.HardnessChainV1 OrdinaryNegativeCubicGadgets
namespace T
export GlobalCloseCompletionKleinTwistedAlgebra (normal Z)
end T
namespace O
export GlobalCloseCompletionC2OrdinaryDenseOrbit (swap_bc swap_bd)
end O
namespace S
export GlobalCloseCompletionC2SignedSixSquare (signed swap_last)
end S
namespace Anchor
export GlobalCloseCompletionC2SparsePrimeAnchors (reindex_prime pair eo signed)
end Anchor
namespace E
export GlobalCloseCompletionC2OrdinaryPairOutcome (HasEq4)
end E
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s r degree : ℕ} {a b : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
variable (K : IntermediateField ℚ AlgebraicComplex)
local instance : Algebra ℚ K := K.algebra'
variable (F : FixedField K degree) (H : (i : Fin r)→Signature K (b i.val))
variable (back : LengthControlledOracleReduction (RawClosedNetwork.validatedEncoding r 1 b) F.encoding
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
    ((QuaternaryOrdinaryCompanion.tables F H).evaluate F) (OriginalForestSource.value G))
variable (z : Fin r) (literal : (⟨b z.val,H z⟩ : AnySignature K)=⟨2,fun x=>T.Z (x 0) (x 1)⟩)

def Outcome : Prop := E.HasEq4 H ∨ Tract (GlobalCloseCompletionUnaryDescentSource.ambient K H) ∨ NoXWeightedAntiSquares.Hard G

include back literal in
theorem normal (N : Macro H 4) (A B C D : K) (form : N.network.denote=T.normal A B C D)
    (prime : Prime (⟨4,N.network.denote⟩ : AnySignature K)) : Outcome G K H := by
  by_cases ha : A=0
  · subst A
    by_cases hb : B=0
    · subst B
      exact Or.inl (Anchor.eo H z literal N C D form prime)
    by_cases hc : C=0
    · subst C
      exact Or.inl (Anchor.eo H z literal (N.reindex (Equiv.swap 1 2)) B D
        (by rw [Macro.reindex_denote,form,O.swap_bc]) (Anchor.reindex_prime H N prime _))
    by_cases hd : D=0
    · subst D
      exact Or.inl (Anchor.eo H z literal (N.reindex (Equiv.swap 1 3)) C B
        (by rw [Macro.reindex_denote,form,O.swap_bd]) (Anchor.reindex_prime H N prime _))
    exact Or.inr (GlobalCloseCompletionC2OrdinaryThreeTerminal.zero_endpoint G K F H back z literal N B C D hb hc hd form)
  by_cases hb : B=0
  · subst B
    by_cases hc : C=0
    · subst C
      exact Or.inl (Anchor.pair H z literal N A D form prime)
    by_cases hd : D=0
    · subst D
      let Q := (N.reindex (Equiv.swap 1 2)).reindex (Equiv.swap 1 3)
      have hQ : Q.network.denote=T.normal A 0 0 C := by
        rw [Macro.reindex_denote,Macro.reindex_denote,form,O.swap_bc,O.swap_bd]
      exact Or.inl (Anchor.pair H z literal Q A C hQ (Anchor.reindex_prime H _ (Anchor.reindex_prime H N prime _) _))
    exact Or.inr (GlobalCloseCompletionC2OrdinaryThreeTerminal.endpoint_live G K F H back z literal N A 0 C D ha hc hd form)
  by_cases hc : C=0
  · subst C
    by_cases hd : D=0
    · subst D
      exact Or.inl (Anchor.pair H z literal (N.reindex (Equiv.swap 1 3)) A B
        (by rw [Macro.reindex_denote,form,O.swap_bd]) (Anchor.reindex_prime H N prime _))
    exact Or.inr (GlobalCloseCompletionC2OrdinaryThreeTerminal.endpoint_live G K F H back z literal
      (N.reindex (Equiv.swap 1 2)) A 0 B D ha hb hd (by rw [Macro.reindex_denote,form,O.swap_bc]))
  exact Or.inr (GlobalCloseCompletionC2OrdinaryThreeTerminal.endpoint_live G K F H back z literal
    (N.reindex (Equiv.swap 1 3)) A D C B ha hc hb (by rw [Macro.reindex_denote,form,O.swap_bd]))

include back literal in
theorem signed (N : Macro H 4) (B C D : K) (form : N.network.denote=S.signed B C D)
    (prime : Prime (⟨4,N.network.denote⟩ : AnySignature K)) : Outcome G K H := by
  by_cases hb : B=0
  · subst B
    exact Or.inl (Anchor.eo H z literal N C D (by simpa only [S.signed,T.normal,neg_zero] using form) prime)
  by_cases hd : D=0
  · subst D
    exact Or.inl (Anchor.signed H N B C form prime)
  by_cases hc : C=0
  · subst C
    exact Or.inl (Anchor.signed H (N.reindex (Equiv.swap 2 3)) B D
      (by rw [Macro.reindex_denote,form,S.swap_last]) (Anchor.reindex_prime H N prime _))
  exact Or.inr (GlobalCloseCompletionC2SignedSixTerminal.live G K F H back z literal N B C D hb hc hd form)

include back literal in
theorem shape (N : Macro H 4)
    (shape : GlobalCloseCompletionC2Q4Charts.Shape (RingHomRealization.mapSignature K.subtype N.network.denote))
    (prime : Prime (⟨4,N.network.denote⟩ : AnySignature K)) : Outcome G K H := by
  rcases shape with ⟨A,B,C,D,form⟩|⟨B,C,D,form⟩
  · exact normal G K F H back z literal N _ _ _ _
      (GlobalCloseCompletionC2OrdinaryShape.normal_form K H N A B C D form) prime
  · exact signed G K F H back z literal N _ _ _
      (GlobalCloseCompletionC2OrdinaryShape.signed_form K H N B C D form) prime

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2CanonicalPrime
end
