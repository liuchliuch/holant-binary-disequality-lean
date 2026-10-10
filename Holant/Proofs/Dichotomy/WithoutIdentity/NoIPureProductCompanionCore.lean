import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPureProductCompression
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPureProductFace
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPureProductFourth
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPureProductPositive
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPureGraphPredicates
import Holant.Proofs.Dichotomy.WithoutIdentity.NoINativeLiteral
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPureProductColumns

/-! An independent non-Product paired companion. Non-affineness is never
used as evidence of non-Product: the original non-Product row is selected
separately, and its fourth power or a signed full binary face is rendered. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureProductCompanion
open Holant Holant.Tractable Holant.Algebraic
namespace C
export NoIPureProductCompression (output mapped_value)
end C
namespace P
export NoIPurePairedHardForm (paired)
end P
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 600000
set_option Elab.async false
variable (target : NoIOrdinaryRaw.Target) (D : NoIPureSquareData.Data target)
local instance : Algebra ℚ D.K:=D.K.algebra'

structure Witness where
  arity : ℕ
  logical : Signature AlgebraicComplex arity
  graph : NativeAntiTargetSource.Output D.table (arity*2)
  value : (fun z=>(graph.network.denote z : AlgebraicComplex))=P.paired logical
  nonproduct : ¬Product logical

def produce {n : ℕ} (N : NativeAntiTargetSource.Output D.table n)
    (bad : ¬Product (fun z=>(N.network.denote z : AlgebraicComplex)))
    (uniform : NoIPureChargeTwoFamily.UniformFour N.network.denote) : Witness target D := by
  classical
  let f : Signature AlgebraicComplex n:=fun z=>(N.network.denote z : AlgebraicComplex)
  by_cases fourth : Product (fun z=>f z^4)
  · let B:=NoIPureProductFace.extract f bad fourth
    have mappedUniform : NoIPureChargeTwoFamily.UniformFour f := by
      intro x y hx hy
      exact uniform x y ((map_ne_zero D.K.val.toRingHom).mp hx)
        ((map_ne_zero D.K.val.toRingHom).mp hy)
    have legal : ∀j,NoIPureCompressionGraph.column B.base B.ports j%4=0:=
      NoIPureProductColumns.divisible f B.base B.ports mappedUniform B.full
    exact {
      arity:=2
      logical:=B.binary
      graph:=C.output target D N B.base B.ports legal
      value:=C.mapped_value target D N B.base B.ports legal
      nonproduct:=B.nonproduct }
  · let N4:=NoIPureProductFourth.output D.table N
    let legal : ∀j,NoIPureCompressionGraph.column (fun _=>false) NoIPureProductFourth.ports j%4=0:=
      NoIPureProductFourth.divisible (n:=n)
    let M:=C.output target D N4 (fun _=>false) NoIPureProductFourth.ports legal
    have form : (fun z=>(M.network.denote z : AlgebraicComplex))=P.paired (fun z=>f z^4) := by
      rw [C.mapped_value]
      apply congrArg P.paired
      funext z
      change D.K.val.toRingHom ((NoIPureProductFourth.output D.table N).network.denote
        (NoIPureProductFourth.S.signedWord (fun _=>false) NoIPureProductFourth.ports z))=f z^4
      rw [NoIPureProductFourth.value]
      exact map_pow D.K.val.toRingHom _ 4
    exact { arity:=n,logical:=fun z=>f z^4,graph:=M,value:=form,nonproduct:=fourth }

def of_not_whole (bad : ¬NoIPureProductPositive.WholeProduct target D)
    (uniform : NoIPureSquareFour.GraphFour target D) : Witness target D := by
  classical
  let existsRow:=not_forall.mp bad
  let j:=Classical.choose existsRow
  have hj:=Classical.choose_spec existsRow
  let N:=NoIPureOddSource.literal D.table j
  exact produce target D N (by simpa only [N,NoIPureOddSource.literal_value] using hj) (uniform _ N)


theorem exists_companion (bad : ¬NoIPureProductPositive.WholeProduct target D)
    (uniform : NoIPureSquareFour.GraphFour target D) :
    ∃m,∃h : Signature AlgebraicComplex m,∃N : NativeAntiTargetSource.Output D.table (m*2),
      (fun z=>(N.network.denote z : AlgebraicComplex))=P.paired h ∧ ¬Product h := by
  let W:=of_not_whole target D bad uniform
  exact ⟨W.arity,W.logical,W.graph,W.value,W.nonproduct⟩


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureProductCompanion
end
