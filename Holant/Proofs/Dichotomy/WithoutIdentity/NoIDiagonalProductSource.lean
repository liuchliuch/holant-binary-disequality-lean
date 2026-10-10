import Holant.Proofs.Dichotomy.WithoutIdentity.NoIBinaryFactor
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIWeightedEqualitySource
import Holant.Proofs.Dichotomy.Native.NativeNormalizedGraphAdjoin

/-! An actual product of two nonsingular diagonal binaries supplies literal
I through complete factor exposure, retaining all original rows and control. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIDiagonalProductSource
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.Hardness.EightVertexNonexception
namespace A
export NativeNormalizedGraphAdjoin (signatures old old_literal newLabel normalized_literal source)
end A
namespace B
export NoIBinaryFactor (extended source old_literal new_literal)
end B
namespace W
export NoIWeightedEqualityFrame (signature)
end W
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option Elab.async false
variable {s degree : ℕ} {arity : ℕ→ℕ}
variable (L : IntermediateField ℚ AlgebraicComplex)
local instance : Algebra ℚ L:=L.algebra'
variable (H : (i : Fin s)→Signature L (arity i.val)) (F : FixedField L degree)

def diagonal (p q : L) : Signature L 2:=
  fun x=>if x 0=x 1 then (if x 0 then q else p) else 0

variable (N : NativeAntiTargetSource.Output H 4) (scale p q u v : L)
variable (scale_ne : scale≠0) (pn : p≠0) (qn : q≠0) (un : u≠0) (vn : v≠0)
variable (form : N.network.denote=fun x=>scale*Signature.tensor (diagonal L p q) (diagonal L u v) x)

def produce : NoISuppliedIdentityData.Data L H F := by
  let J:=A.signatures F H N scale
  let k:=A.newLabel H
  let f:=diagonal L p q
  let g:=diagonal L u v
  let row:=Signature.tensor f g
  have literal : (⟨NativeNormalizedGraphAdjoin.arity H N k.val,J k⟩ : AnySignature L)=⟨4,row⟩ :=
    A.normalized_literal F H N scale row scale_ne form
  have first : (entries row).a≠0 := by
    simpa [row,f,g,diagonal,entries,Signature.tensor_apply] using mul_ne_zero pn un
  have last : (entries row).x≠0 := by
    simpa [row,f,g,diagonal,entries,Signature.tensor_apply] using mul_ne_zero qn vn
  have gn : g≠0 := by
    intro h
    have zero:=congrFun h ![false,false]
    exact un (by simpa [g,diagonal] using zero)
  let J2:=B.extended J f
  let j2 : Fin (s+2):=⟨s+1,by omega⟩
  have literalF : (⟨NoIBinaryFactor.arity j2.val,J2 j2⟩ : AnySignature L)=⟨2,f⟩ := B.new_literal J f
  have weighted : (⟨NoIBinaryFactor.arity j2.val,J2 j2⟩ : AnySignature L)=
      ⟨2,Holant.Complexity.BinaryInterpolation.Chains.binarySignature (OrdinaryTargetInterpolationDiagonal.diagonal p q)⟩ := by
    rw [literalF]
    rfl
  let D:=NoIWeightedEqualitySource.produce L J2 F j2 p q pn qn weighted
  have old : GlobalCloseCompletionUnaryDescentSource.ambient L H⊆
      GlobalCloseCompletionUnaryDescentSource.ambient L J2 := by
    rintro t ⟨i,rfl⟩
    refine ⟨Fin.castAdd 1 (A.old H i),?_⟩
    exact congrArg (RingHomRealization.mapAny L.subtype)
      ((B.old_literal J f (A.old H i)).trans (A.old_literal F H N scale i))
  exact {
    K:=D.K
    degree:=D.degree
    presentation:=D.presentation
    count:=D.count
    b:=D.b
    table:=D.table
    identity:=D.identity
    identity_literal:=D.identity_literal
    basis:=D.basis
    native:=D.native
    retained:=(Set.image_mono old).trans D.retained
    source:=Programme.compose D.source (Programme.compose
      (B.source J F f g row k k literal first last literal gn)
      (A.source F H N scale scale_ne)) }

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIDiagonalProductSource
end
