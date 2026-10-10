import Holant.Proofs.Dichotomy.Closure.Symmetric.GlobalCloseCompletionSymmetricGHZPreparation
import Holant.Proofs.Dichotomy.Closure.Symmetric.GlobalCloseCompletionSymmetricGHZSemantics
import Holant.Proofs.Dichotomy.Closure.Symmetric.GlobalCloseCompletionSymmetricGHZChart
import Holant.Proofs.Dichotomy.Closure.Symmetric.GlobalCloseCompletionSymmetricGHZRows

/-! The actual inverse source, normalized physical square, and complete-row
chart retain a weighted ternary, the exact Gram row, and every original row. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSymmetricGHZPrepared
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.FinitePGL2.Stabilization OrdinaryNegativeCubicGadgets
namespace Pr
export GlobalCloseCompletionSymmetricGHZPreparation
  (table arity old old_literal hLabel h h_literal h_value inverseLabel inverse_literal gram gramLabel gram_literal source)
end Pr
namespace Ch
export GlobalCloseCompletionSymmetricGHZChart (field presentation table retained_literal controlled)
end Ch
namespace Rt
export GlobalCloseCompletionSymmetricGHZRootInverse (Extension mapped_right)
end Rt
namespace Sem
export GlobalCloseCompletionSymmetricGHZSemantics (normalized_square)
end Sem
namespace Gr
export GlobalCloseCompletionSymmetricGHZGram (scale)
end Gr
namespace Row
export GlobalCloseCompletionSymmetricGHZRows (row value)
end Row
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option maxRecDepth 16384
set_option Elab.async false
variable {r degree : ℕ} {b : ℕ→ℕ}
variable (L : IntermediateField ℚ AlgebraicComplex)
local instance : Algebra ℚ L:=L.algebra'
variable (F : FixedField L degree) (H : (i : Fin r)→Signature L (b i.val))
variable (N : Macro H 3) (C : NoXOrdinaryGraphAdjoin.Output H 2) (D : Rt.Extension L F H C)
local instance : Algebra ℚ D.K:=D.K.algebra'
variable (R : InvertibleKernel)
abbrev field:=Ch.field D.K (Pr.table L F H N C D) D.inverse R
local instance : Algebra ℚ (field L F H N C D R):=(field L F H N C D R).algebra'
abbrev presentation:=Ch.presentation D.K (Pr.table L F H N C D) D.inverse R
abbrev table:=Ch.table D.K (Pr.table L F H N C D) D.inverse R
abbrev arity:=Pr.arity L F H N C D
def ambient:=GlobalCloseCompletionUnaryDescentSource.ambient (field L F H N C D R) (table L F H N C D R)
variable (normalized : Kernel.pullback (fun p q=>(D.inverse p q : AlgebraicComplex)) R.matrix=Signature.equality)

def source : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding (D.count+1+1) 1 (arity L F H N C D)) (presentation L F H N C D R).encoding
    (RawClosedNetwork.validatedEncoding r 1 b) F.encoding
    ((QuaternaryOrdinaryCompanion.tables (presentation L F H N C D R) (table L F H N C D R)).evaluate
      (presentation L F H N C D R))
    ((QuaternaryOrdinaryCompanion.tables F H).evaluate F) :=
  Programme.compose (Ch.controlled D.K D.presentation (Pr.table L F H N C D) D.inverse R normalized
    (Pr.inverseLabel L F H N C D) (Pr.inverse_literal L F H N C D)) (Pr.source L F H N C D)

theorem retained {n : ℕ} (f : Signature AlgebraicComplex n)
    (member : (⟨n,f⟩ : AnySignature AlgebraicComplex)∈GlobalCloseCompletionUnaryDescentSource.ambient L H) :
    (⟨n,R.symm.action f⟩ : AnySignature AlgebraicComplex)∈ambient L F H N C D R := by
  rcases member with ⟨i,hi⟩
  refine ⟨Pr.old L F H N C D i,?_⟩
  exact Ch.retained_literal D.K (Pr.table L F H N C D) D.inverse R _ f
    ((Pr.old_literal L F H N C D i).trans hi)

theorem included : familyAction R.symm (GlobalCloseCompletionUnaryDescentSource.ambient L H)⊆
    ambient L F H N C D R := by
  rintro _ ⟨⟨n,f⟩,member,rfl⟩
  exact retained L F H N C D R f member

theorem h_literal :
    RingHomRealization.mapAny (field L F H N C D R).subtype
      (⟨arity L F H N C D (Pr.hLabel L F H N C D).val,
        table L F H N C D R (Pr.hLabel L F H N C D)⟩ : AnySignature (field L F H N C D R))=
      ⟨3,R.symm.action (RingHomRealization.mapSignature L.subtype N.network.denote)⟩ := by
  apply Ch.retained_literal
  exact (congrArg (RingHomRealization.mapAny D.K.subtype) (Pr.h_literal L F H N C D)).trans
    (congrArg (fun f : Signature AlgebraicComplex 3=>(⟨3,f⟩ : AnySignature AlgebraicComplex))
      (Pr.h_value L F H N C D))

def ternary : Macro (table L F H N C D R) 3:=
  Row.row (field L F H N C D R).subtype (table L F H N C D R) (Pr.hLabel L F H N C D) _
    (h_literal L F H N C D R)

theorem ternary_value : RingHomRealization.mapSignature (field L F H N C D R).subtype
    (ternary L F H N C D R).network.denote=
      R.symm.action (RingHomRealization.mapSignature L.subtype N.network.denote) :=
  Row.value (field L F H N C D R).subtype (table L F H N C D R) (Pr.hLabel L F H N C D) _
    (h_literal L F H N C D R)

def original : Kernel AlgebraicComplex:=fun p q=>(D.original p q : AlgebraicComplex)
theorem right_inverse : Kernel.mul (original L F H C D)
    (fun p q=>(D.inverse p q : AlgebraicComplex))=Gr.scale (D.scalar : AlgebraicComplex) Signature.equality := by
  have h:=Rt.mapped_right L F H C D
  rw [←D.original_value] at h
  funext p q
  have e:=congrFun₂ h p q
  simpa [original,Kernel.mul,Matrix.mul_apply,Matrix.map_apply,Matrix.one_apply,Gr.scale,Signature.equality] using e

theorem square_value : RingHomRealization.mapSignature D.K.subtype (binarySignature (Pr.gram L F H C D))=
    kernelSignature (Gr.scale ((D.scalar : AlgebraicComplex)^2)⁻¹
      (Kernel.mul (original L F H C D) (original L F H C D))) := by
  funext x
  change D.K.subtype ((D.scalar^2)⁻¹*(D.original*D.original) (x 0) (x 1))=_
  simp only [map_mul,map_inv,map_pow,Matrix.mul_apply,map_sum]
  rfl

include normalized in
theorem gram_literal :
    RingHomRealization.mapAny (field L F H N C D R).subtype
      (⟨arity L F H N C D (Pr.gramLabel L F H N C D).val,
        table L F H N C D R (Pr.gramLabel L F H N C D)⟩ : AnySignature (field L F H N C D R))=
      ⟨2,kernelSignature (Kernel.pullback Signature.equality R.matrix)⟩ := by
  have literal:=Ch.retained_literal D.K (Pr.table L F H N C D) D.inverse R (Pr.gramLabel L F H N C D)
    (RingHomRealization.mapSignature D.K.subtype (binarySignature (Pr.gram L F H C D)))
    (congrArg (RingHomRealization.mapAny D.K.subtype) (Pr.gram_literal L F H N C D))
  rw [square_value L F H C D,Sem.normalized_square R _ _ (D.scalar : AlgebraicComplex)
    ((map_ne_zero (D.K.val.toRingHom : D.K→+*AlgebraicComplex)).mpr D.nonzero) normalized (right_inverse L F H C D)] at literal
  exact literal

include normalized in
theorem gram_member : (⟨2,kernelSignature (Kernel.pullback Signature.equality R.matrix)⟩ : AnySignature AlgebraicComplex)∈
    ambient L F H N C D R := ⟨Pr.gramLabel L F H N C D,gram_literal L F H N C D R normalized⟩

def gramGraph : Macro (table L F H N C D R) 2:=
  Row.row (field L F H N C D R).subtype (table L F H N C D R) (Pr.gramLabel L F H N C D) _
    (gram_literal L F H N C D R normalized)

theorem gram_value : RingHomRealization.mapSignature (field L F H N C D R).subtype
    (gramGraph L F H N C D R normalized).network.denote=
      kernelSignature (Kernel.pullback Signature.equality R.matrix) :=
  Row.value (field L F H N C D R).subtype (table L F H N C D R) (Pr.gramLabel L F H N C D) _
    (gram_literal L F H N C D R normalized)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSymmetricGHZPrepared
end
