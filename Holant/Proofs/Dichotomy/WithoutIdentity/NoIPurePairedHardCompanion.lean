import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPurePairedHard
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPureProductCompanionCore

/-! A non-A paired graph and an independently produced non-P companion
are compiled jointly to the unchanged target. Under nonhardness this forces
all physically legal signed compressions to be Affine. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePairedHardCompanion
open Holant Holant.Tractable Holant.Algebraic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option Elab.async false
variable (target : NoIOrdinaryRaw.Target) (D : NoIPureSquareData.Data target)
local instance : Algebra ℚ D.K:=D.K.algebra'
variable (badP : ¬NoIPureProductPositive.WholeProduct target D)
variable (uniform : NoIPureSquareFour.GraphFour target D)
include badP uniform

/-- The independent companion may have a different logical arity. -/
theorem hard {m : ℕ} (h : Signature AlgebraicComplex m)
    (N : NativeAntiTargetSource.Output D.table (m*2))
    (form : (fun z=>(N.network.denote z : AlgebraicComplex))=NoIPurePairedHardForm.paired h)
    (badA : ¬Affine h) : target.Hard := by
  obtain ⟨n,g,M,fg,ng⟩:=NoIPureProductCompanion.exists_companion target D badP uniform
  exact NoIPurePairedHard.two target D h g N M form fg badA ng

theorem affine (noHard : ¬target.Hard) {m : ℕ} (h : Signature AlgebraicComplex m)
    (N : NativeAntiTargetSource.Output D.table (m*2))
    (form : (fun z=>(N.network.denote z : AlgebraicComplex))=NoIPurePairedHardForm.paired h) :
    Affine h := by
  by_contra badA
  exact noHard (hard target D badP uniform h N form badA)

/-- The logical row is read from one actual graph using legal signed port
multiplicities; its physical paired implementation is built internally. -/
theorem signed_affine (noHard : ¬target.Hard) {n m : ℕ}
    (N : NativeAntiTargetSource.Output D.table n)
    (base : Fin n→Bool) (ports : Fin n→Bool⊕Fin m)
    (legal : ∀j,NoIPureCompressionGraph.column base ports j%4=0) :
    Affine (fun z=>(N.network.denote
      (NoIPureCompressionGraph.signedWord base ports z) : AlgebraicComplex)) :=
  affine target D badP uniform noHard _
    (NoIPureProductCompression.output target D N base ports legal)
    (NoIPureProductCompression.mapped_value target D N base ports legal)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePairedHardCompanion
end
