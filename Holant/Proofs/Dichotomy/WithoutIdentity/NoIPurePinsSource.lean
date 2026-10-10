import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPurePinsData
import Holant.Proofs.Dichotomy.Native.NativeFixedFieldRecode
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPureUnaryControl

noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePinsSource
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.Hardness.FrozenFactorNormalization
namespace U
export QuaternaryUnaryAccess (K F paletteArity palette palette_old palette_pin decoded_exact)
end U
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s degree : ℕ} {a : ℕ→ℕ}
variable (L : IntermediateField ℚ AlgebraicComplex)
local instance : Algebra ℚ L:=L.algebra'
variable (H : (i : Fin s)→Signature L (a i.val)) (F : FixedField L degree)
variable (q : Signature L 4) (j : Fin s)
variable (literal : (⟨a j.val,H j⟩ : AnySignature L)=⟨4,q⟩)
variable (pure : Holant.EightVertex.ProductAnchor.PureEquality (RingHomRealization.mapSignature L.subtype q))

def produce : NoIPurePinsData.Data L H F := by
  classical
  apply Classical.choice
  letI : NumberField L:={to_charZero:=inferInstance,to_finiteDimensional:=F.basis.finiteDimensional_of_finite}
  let G:=OriginalLCodec.mapped L.val H
  let P:=QuaternaryEqualityTerminal.pureStep pure
  have hj : (⟨a j.val,G j⟩ : AnySignature AlgebraicComplex)=
      ⟨4,RingHomRealization.mapSignature L.subtype q⟩ :=
    congrArg (RingHomRealization.mapAny L.subtype) literal
  have old (i : Fin s) : RingHomRealization.mapAny (U.K G).subtype
      (⟨U.paletteArity s a i.val,U.palette G ⟨i.val,by omega⟩⟩ : AnySignature (U.K G))=⟨a i.val,G i⟩ := by
    have h:=congrArg (RingHomRealization.mapAny (U.K G).subtype) (U.palette_old G i)
    exact h.trans (congrArg (fun f : Signature AlgebraicComplex (a i.val)=>(⟨a i.val,f⟩ : AnySignature AlgebraicComplex))
      (funext (U.decoded_exact G i)))
  obtain ⟨f,fliteral,fmap⟩:=NoIPurePinsData.lift_four (K:=U.K G) (U.K G).subtype
    (⟨U.paletteArity s a j.val,U.palette G ⟨j.val,by omega⟩⟩ : AnySignature (U.K G))
    (RingHomRealization.mapSignature L.subtype q) ((old j).trans hj)
  exact ⟨{
    K:=U.K G
    degree:=Module.finrank ℚ (U.K G)
    presentation:=U.F G
    count:=s+2
    arity:=U.paletteArity s a
    table:=U.palette G
    retained:=by
      rintro t ⟨i,rfl⟩
      exact ⟨⟨i.val,by omega⟩,old i⟩
    pin:=fun b=>⟨s+b.toNat,by cases b <;> simp <;> omega⟩
    pin_literal:=U.palette_pin G
    q:=f
    label:=⟨j.val,by omega⟩
    literal:=fliteral
    pure:=by rw [fmap];exact pure
    source:=Programme.compose (NoIPureUnaryControl.SourceV2.source L.val H j hj P)
      (NativeFixedFieldRecode.controlled H (OriginalLCodec.presentation (L:=L)) F) }⟩

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePinsSource
end
