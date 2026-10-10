import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2SignedSixTerminal
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2SignedSixAffine
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2OrdinaryQuaternary

/-! All coefficient degeneracies of the actual canonical signed six-vertex
source are consumed. Fourth-root sparse residuals retain their genuine Affine
witness; every nonaffine arm closes the complete unchanged source family. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2SignedSixClassified
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1 OrdinaryNegativeCubicGadgets
namespace T
export GlobalCloseCompletionKleinTwistedAlgebra (normal Z)
end T
namespace S
export GlobalCloseCompletionC2SignedSixSquare (signed square side side_square swap_last)
end S
namespace Q
export GlobalCloseCompletionC2OrdinaryQuaternary (Outcome reindex_back)
end Q
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

theorem mapped_signed (B C D : K) : RingHomRealization.mapSignature K.subtype (S.signed (K:=K) B C D)=
    S.signed (K:=AlgebraicComplex) (B:AlgebraicComplex) (C:AlgebraicComplex) (D:AlgebraicComplex) := by
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [RingHomRealization.mapSignature,S.signed,Holant.LocalDrafts.Hardness.EightVertexNonexception.table,h0,h1,h2,h3] <;> rfl

include back zLiteral in
theorem two_live (N : Macro H 4) (B C : K) (hB : B≠0) (hC : C≠0)
    (form : N.network.denote=S.signed B C 0) : Q.Outcome G K H N := by
  by_cases fourth : B^4=C^4
  · left
    rw [form,mapped_signed]
    exact GlobalCloseCompletionC2SignedSixAffine.sparse_affine _ _
      (by intro zero; exact hC (Subtype.ext zero)) (by exact congrArg K.subtype fourth)
  right
  have h : (S.square H (S.side H N)).network.denote=T.normal (C^2) 0 (B^2) 0 := by
    simpa using S.side_square H N B C 0 form
  apply GlobalCloseCompletionC2SignedSixTerminal.finish G K F H back z zLiteral
    (S.square H (S.side H N)) (C^2) (B^2) h
    (by
      intro eqn
      apply fourth
      calc
        B^4=(B^2)^2 := by ring
        _=(C^2)^2 := eqn.symm
        _=C^4 := by ring)
    (N.reindex (Equiv.swap 1 3)) C B hC hB
  intro x
  rw [Macro.reindex_denote,form]
  cases h0 : x 0 <;> cases h1 : x 1 <;>
    simp [Tensor.reindex,Equiv.swap_apply_def,S.signed,Holant.LocalDrafts.Hardness.EightVertexNonexception.table,
      NoXWeightedAntiSigned.anti,h0,h1]

include back zLiteral in
theorem classified (N : Macro H 4) (B C D : K) (form : N.network.denote=S.signed B C D) : Q.Outcome G K H N := by
  by_cases hb : B=0
  · subst B
    apply GlobalCloseCompletionC2OrdinaryQuaternary.eo G K F H back z zLiteral N C D
    simpa only [S.signed,T.normal,neg_zero] using form
  by_cases hd : D=0
  · subst D
    by_cases hc : C=0
    · subst C
      left
      rw [form,mapped_signed]
      exact GlobalCloseCompletionC2SignedSixAffine.sparse_zero_affine _
    exact two_live G K F H back z zLiteral N B C hb hc form
  by_cases hc : C=0
  · subst C
    apply Q.reindex_back G K H N (Equiv.swap 2 3)
    exact two_live G K F H back z zLiteral (N.reindex (Equiv.swap 2 3)) B D hb hd
      (by rw [Macro.reindex_denote,form,S.swap_last])
  exact Or.inr (GlobalCloseCompletionC2SignedSixTerminal.live G K F H back z zLiteral N B C D hb hc hd form)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2SignedSixClassified
end
