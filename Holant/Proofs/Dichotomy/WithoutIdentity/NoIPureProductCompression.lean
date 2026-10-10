import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPureCompressionSource
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPureProductPaired
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPureSquareResources

/-! Signed compression specialized to the actual retained pure alphabet.
Eq4, X and both pins are literal rows of that same exact native table. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureProductCompression
open Holant Holant.Tractable Holant.Algebraic
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
set_option Elab.async false
variable (target : NoIOrdinaryRaw.Target) (D : NoIPureSquareData.Data target)
local instance : Algebra ℚ D.K:=D.K.algebra'

def x : NativeAntiTargetSource.Output D.table 2 where
  network:=Network.corolla (fun z=>Signature.disequality (z 0) (z 1))
  labels:={vertex _:=D.x
           vertex_arity _:=congrArg Sigma.fst D.x_literal
           edge:=Fin.elim0}
  exact:=fun _=>D.x_literal
  native:=fun e=>Fin.elim0 e

theorem x_form : (x target D).network.denote=fun z=>Signature.disequality (z 0) (z 1):=
  Network.denote_corolla _

theorem eq4_form : (NoIPureSquareParity.eq4 target D).network.denote=
    Holant.EightVertex.ProductAnchor.equalityFour:=Network.denote_corolla _

variable {n m : ℕ} (N : NativeAntiTargetSource.Output D.table n)
variable (base : Fin n→Bool) (ports : Fin n→Bool⊕Fin m)
variable (legal : ∀j,NoIPureCompressionGraph.column base ports j%4=0)

def output : NativeAntiTargetSource.Output D.table (m*2):=
  NoIPureCompressionSource.output D.table (NoIPureSquareParity.eq4 target D) (x target D)
    (NoIPureSquareParity.pins target D) (eq4_form target D) (x_form target D) N base ports legal

theorem value : (output target D N base ports legal).network.denote=
    NoIPurePairedHardForm.paired
      (fun z=>N.network.denote (NoIPureCompressionGraph.signedWord base ports z)) :=
  NoIPureCompressionSource.value D.table (NoIPureSquareParity.eq4 target D) (x target D)
    (NoIPureSquareParity.pins target D) (eq4_form target D) (x_form target D)
    (NoIPureSquareParity.pins_form target D) N base ports legal

theorem mapped_value :
    (fun z=>((output target D N base ports legal).network.denote z : AlgebraicComplex))=
      NoIPurePairedHardForm.paired
        (fun z=>(N.network.denote (NoIPureCompressionGraph.signedWord base ports z) : AlgebraicComplex)) := by
  funext z
  rw [value]
  exact NoIPureProductPaired.map_paired D.K.val.toRingHom _ z

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureProductCompression
end
