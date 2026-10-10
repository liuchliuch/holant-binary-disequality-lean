import Holant.Proofs.Dichotomy.Main.PaperControlledHardness
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2OrdinaryNativeSource
import Holant.Proofs.Dichotomy.Main.PaperControlled.C2NativeEq4Terminal
import Holant.Proofs.Dichotomy.Closure.Sparse.GlobalCloseCompletionSparseEq4Flip
import Holant.Proofs.Reductions.FrozenFactorNormalization.NormalizedTree

/-! A native finite power returned from the exact inverse-K source is closed
using the retained old Z row, whose inverse-K image is literally I. Actual
I legs convert DEQ to Eq4 and the whole old ordinary criterion is recovered. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlled.C2OrdinaryNativeEq4
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity FixedGadgetSubstitution
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
namespace S
export GlobalCloseCompletionC2OrdinaryNativeSource (mapped native field presentation table table_value source)
end S
namespace L
export GlobalCloseCompletionSparseEq4Flip (identity leg legLabels leg_exact leg_native equality_denote)
end L
namespace T
export GlobalCloseCompletionKleinTwistedAlgebra (Z)
end T
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s r degree : ℕ} {a b : ℕ→ℕ}
variable (K : IntermediateField ℚ AlgebraicComplex)
local instance : Algebra ℚ K := K.algebra'
variable (F : FixedField K degree) (H : (i : Fin r)→Signature K (b i.val))
local instance : Algebra ℚ (S.field K H) := (S.field K H).algebra'
variable (z : Fin r) (zLiteral : (⟨b z.val,H z⟩ : AnySignature K)=⟨2,fun x=>T.Z (x 0) (x 1)⟩)

include zLiteral in
theorem identity_ambient : (⟨b z.val,S.native K H z⟩ : AnySignature AlgebraicComplex)=
    ⟨2,kernelSignature Signature.equality⟩ := by
  have h := congrArg (fun f : AnySignature AlgebraicComplex=>
    (⟨f.1,sourceKBasis.symm.action f.2⟩ : AnySignature AlgebraicComplex))
      (congrArg (RingHomRealization.mapAny K.subtype) zLiteral)
  refine h.trans ?_
  have mapped : RingHomRealization.mapSignature K.subtype (fun x : Fin 2→Bool=>T.Z (K:=K) (x 0) (x 1))=zAnchor := by
    funext x
    cases h0 : x 0 <;> cases h1 : x 1 <;>
      simp [RingHomRealization.mapSignature,T.Z,zAnchor,kernelSignature,diagonalKernel,h0,h1]
  change (⟨2,sourceKBasis.symm.action (RingHomRealization.mapSignature K.subtype
    (fun x : Fin 2→Bool=>T.Z (K:=K) (x 0) (x 1)))⟩ : AnySignature AlgebraicComplex)=_
  rw [mapped,sourceKBasis_symm_action_zAnchor]

include zLiteral in
theorem identity_literal : (⟨b z.val,S.table K H z⟩ : AnySignature (S.field K H))=⟨2,L.identity⟩ := by
  apply Holant.LocalDrafts.Hardness.FrozenFactorNormalization.mapAny_injective (S.field K H).subtype
  refine (identity_ambient K H z zLiteral).trans ?_
  apply congrArg (fun f : Signature AlgebraicComplex 2=>(⟨2,f⟩ : AnySignature AlgebraicComplex))
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;>
    simp [kernelSignature,L.identity,RingHomRealization.mapSignature,Signature.equality,h0,h1]

variable (D : GeneralEODEQProducerNormalize.Produced (S.table K H))
def first := L.leg D.network false
def firstLabels := L.legLabels D.network D.labels z (congrArg Sigma.fst (identity_literal K H z zLiteral)) false
def graph := L.leg (first K H D) true
def labels := L.legLabels (first K H D) (firstLabels K H z zLiteral D) z
  (congrArg Sigma.fst (identity_literal K H z zLiteral)) true

theorem exact : LabelledNetwork.Exact (S.table K H) (graph K H D) (labels K H z zLiteral D) :=
  L.leg_exact (S.table K H) _ _
    (L.leg_exact (S.table K H) D.network D.labels D.exact z (identity_literal K H z zLiteral) false)
    z (identity_literal K H z zLiteral) true

theorem native : ∀e,(graph K H D).edge e=Signature.disequality :=
  L.leg_native _ (L.leg_native D.network D.native false) true

theorem denote : (graph K H D).denote=D.scalar • Holant.EightVertex.ProductAnchor.equalityFour :=
  L.equality_denote D.network D.scalar D.denote

include zLiteral D in
theorem actual : Gadget.RealizesUpTo (UniversalPairReduction.FiniteFamily.family (S.native K H)) .disequality
    (Holant.EightVertex.ProductAnchor.equalityFour (K:=AlgebraicComplex)) := by
  refine ⟨(D.scalar : AlgebraicComplex),?_,?_⟩
  · intro zero
    exact D.nonzero (Subtype.ext zero)
  have den : ((graph K H D).map (S.field K H).subtype).denote=
      (fun x=>(D.scalar : AlgebraicComplex)*Holant.EightVertex.ProductAnchor.equalityFour x) := by
    funext x
    rw [Network.denote_map,denote]
    change (S.field K H).subtype (D.scalar*Holant.EightVertex.ProductAnchor.equalityFour x)=_
    rw [map_mul]
    congr 1
    unfold Holant.EightVertex.ProductAnchor.equalityFour
    split_ifs <;> rfl
  rw [←den]
  apply Gadget.realizes_network _ _ .disequality
  · intro v
    refine ⟨(labels K H z zLiteral D).vertex v,?_⟩
    exact congrArg (RingHomRealization.mapAny (S.field K H).subtype) (exact K H z zLiteral D v)
  · intro e
    funext u v
    change (S.field K H).subtype ((graph K H D).edge e u v)=Signature.disequality u v
    rw [native]
    cases u <;> cases v <;> rfl

variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
variable (back : LengthControlledOracleReduction (RawClosedNetwork.validatedEncoding r 1 b) F.encoding
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
    ((QuaternaryOrdinaryCompanion.tables F H).evaluate F) (OriginalForestSource.value G))

def input : GlobalCloseCompletionKleinFiniteEq4.Input G where
  count := r
  arity := b
  table := S.native K H
  identity := ⟨z,identity_ambient K H z zLiteral⟩
  source := Programme.compose (S.source K F H) back

theorem family_exact : familyAction sourceKBasis (UniversalPairReduction.FiniteFamily.family (S.native K H))=
    UniversalPairReduction.FiniteFamily.family (S.mapped K H) := by
  ext f
  constructor
  · rintro ⟨g,⟨i,rfl⟩,rfl⟩
    refine ⟨i,?_⟩
    simp [S.native,KSourceTransport.nativeSignatures]
  · rintro ⟨i,rfl⟩
    refine ⟨⟨b i.val,S.native K H i⟩,⟨i,rfl⟩,?_⟩
    simp [S.native,KSourceTransport.nativeSignatures]

include zLiteral D back in
theorem classified : Tract (UniversalPairReduction.FiniteFamily.family (S.mapped K H)) ∨
    PaperControlledHardness.Original G := by
  have h := PaperControlled.C2NativeEq4Terminal.classified G (input K F H z zLiteral G back)
    (actual K H z zLiteral D)
  change Tract (familyAction sourceKBasis (UniversalPairReduction.FiniteFamily.family (S.native K H))) ∨
    PaperControlledHardness.Original G at h
  rw [family_exact] at h
  exact h

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlled.C2OrdinaryNativeEq4
end
