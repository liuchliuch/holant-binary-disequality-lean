import Holant.Proofs.Dichotomy.Main.PaperControlledHardness
import Holant.Proofs.Dichotomy.Main.PaperControlled.C2OrdinaryThreeTerminal
import Holant.Proofs.Dichotomy.Main.PaperControlled.C2OrdinaryEOTerminal
import Holant.Proofs.Dichotomy.Main.PaperControlled.C2UnsignedPairOutcome

/-! Exhaustive actual ordinary complementary-even q4 classification. Every
coefficient pattern has either a literal affine witness, a whole-source
tractability certificate, or a reduction to the unchanged original input. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlled.C2OrdinaryQuaternary
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1 OrdinaryNegativeCubicGadgets
namespace T
export GlobalCloseCompletionKleinTwistedAlgebra (normal Z)
end T
namespace O
export GlobalCloseCompletionC2OrdinaryDenseOrbit (swap_bc swap_bd)
end O
namespace P
export GlobalCloseCompletionKleinOrdinaryPair (pair symmetric pairOrder normal_pair)
end P
namespace M
export GeneralEOAffinePlaneChain (binary bitIndex)
end M
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
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
variable (z : Fin r) (zLiteral : (⟨b z.val,H z⟩ : AnySignature K)=⟨2,fun x=>T.Z (x 0) (x 1)⟩)

def Outcome (N : Macro H 4) : Prop :=
  Affine (RingHomRealization.mapSignature K.subtype N.network.denote) ∨
    Tract (GlobalCloseCompletionUnaryDescentSource.ambient K H) ∨
      PaperControlledHardness.Original G

theorem reindex_back (N : Macro H 4) (e : Equiv.Perm (Fin 4))
    (h : Outcome G K H (N.reindex e)) : Outcome G K H N := by
  rcases h with h|h
  · left
    have ha := h.precompose (fun x i=>x (e.symm i)) (coordinates_isAffineMap e.symm)
    convert ha using 1
    funext x
    simp only [RingHomRealization.mapSignature,Macro.reindex_denote,Tensor.reindex,Equiv.symm_apply_apply]
  · exact Or.inr h

include back in
theorem endpoint_pair (N : Macro H 4) (A D : K) (form : N.network.denote=T.normal A 0 0 D) :
    Outcome G K H N := by
  apply reindex_back G K H N P.pairOrder
  rcases PaperControlled.C2UnsignedPairOutcome.affine_or_hard F H K.subtype
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
    (OriginalForestSource.value G) back (N.reindex P.pairOrder) A D
    (by rw [Macro.reindex_denote,form,P.normal_pair]) with affine|hard
  · exact Or.inl affine
  · exact Or.inr (Or.inr hard)

theorem eo_of_affine (N : Macro H 4) (C D : K) (form : N.network.denote=T.normal 0 0 C D)
    (h : Affine (M.binary (P.symmetric (C:AlgebraicComplex) (D:AlgebraicComplex)))) : Outcome G K H N := by
  left
  have affine := EOBinaryPlaneTract.affine_lift h
  convert affine using 1
  funext x
  rw [form]
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [RingHomRealization.mapSignature,T.normal,Holant.LocalDrafts.Hardness.EightVertexNonexception.table,
      EOBinaryPlaneCore.lift,M.binary,M.bitIndex,P.symmetric,h0,h1,h2,h3] <;> rfl

include back zLiteral in
theorem eo (N : Macro H 4) (C D : K) (form : N.network.denote=T.normal 0 0 C D) : Outcome G K H N := by
  by_cases hc : C=0
  · apply eo_of_affine G K H N C D form
    simpa only [hc,ZeroMemClass.coe_zero] using GlobalCloseCompletionC2PairAffine.anti_affine (D:AlgebraicComplex)
  by_cases hd : D=0
  · apply eo_of_affine G K H N C D form
    simpa only [hd,ZeroMemClass.coe_zero] using GlobalCloseCompletionC2PairAffine.diagonal_affine (C:AlgebraicComplex)
  exact PaperControlled.C2OrdinaryEOTerminal.classified G K F H back z zLiteral N C D hc hd form

include back zLiteral in
theorem classified (N : Macro H 4) (A B C D : K) (form : N.network.denote=T.normal A B C D) :
    Outcome G K H N := by
  by_cases ha : A=0
  · subst A
    by_cases hb : B=0
    · subst B
      exact eo G K F H back z zLiteral N C D form
    by_cases hc : C=0
    · subst C
      apply reindex_back G K H N (Equiv.swap 1 2)
      exact eo G K F H back z zLiteral (N.reindex (Equiv.swap 1 2)) B D
        (by rw [Macro.reindex_denote,form,O.swap_bc])
    by_cases hd : D=0
    · subst D
      apply reindex_back G K H N (Equiv.swap 1 3)
      exact eo G K F H back z zLiteral (N.reindex (Equiv.swap 1 3)) C B
        (by rw [Macro.reindex_denote,form,O.swap_bd])
    exact Or.inr (PaperControlled.C2OrdinaryThreeTerminal.zero_endpoint G K F H back z zLiteral N B C D hb hc hd form)
  by_cases hb : B=0
  · subst B
    by_cases hc : C=0
    · subst C
      exact endpoint_pair G K F H back N A D form
    by_cases hd : D=0
    · subst D
      apply reindex_back G K H N (Equiv.swap 1 2)
      apply reindex_back G K H (N.reindex (Equiv.swap 1 2)) (Equiv.swap 1 3)
      apply endpoint_pair G K F H back _ A C
      rw [Macro.reindex_denote,Macro.reindex_denote,form,O.swap_bc,O.swap_bd]
    exact Or.inr (PaperControlled.C2OrdinaryThreeTerminal.endpoint_live G K F H back z zLiteral N A 0 C D ha hc hd form)
  by_cases hc : C=0
  · subst C
    by_cases hd : D=0
    · subst D
      apply reindex_back G K H N (Equiv.swap 1 3)
      apply endpoint_pair G K F H back _ A B
      rw [Macro.reindex_denote,form,O.swap_bd]
    exact Or.inr (PaperControlled.C2OrdinaryThreeTerminal.endpoint_live G K F H back z zLiteral
      (N.reindex (Equiv.swap 1 2)) A 0 B D ha hb hd (by rw [Macro.reindex_denote,form,O.swap_bc]))
  exact Or.inr (PaperControlled.C2OrdinaryThreeTerminal.endpoint_live G K F H back z zLiteral
    (N.reindex (Equiv.swap 1 3)) A D C B ha hc hb (by rw [Macro.reindex_denote,form,O.swap_bd]))

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlled.C2OrdinaryQuaternary
end
