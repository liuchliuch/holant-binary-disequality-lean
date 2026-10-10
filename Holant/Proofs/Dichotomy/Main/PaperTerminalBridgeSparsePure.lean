import Holant.Proofs.Dichotomy.Main.PaperTerminalBridgeSparseOrders
import Holant.Proofs.Algorithms.QuaternaryEqualityTerminal

/-! The all-zero-middle endpoint is retained as the genuine pure weighted
Eq4 case. Its two original coefficients and their nonzero values are exact;
no sparse or one-sided consumer is asserted to have covered it. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperTerminalBridgeSparsePure
open Holant Holant.Tractable
open Holant.LocalDrafts.Hardness.EightVertexNonexception
open Holant.LocalDrafts.MainChain
open Holant.EightVertex.ProductAnchor
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
set_option Elab.async false
variable {K : Type} [Field K]
variable (q : Signature K 4) (even : EvenSupport q)
variable (dead : ¬PaperTerminalBridgeSparseOrders.MiddleLive q)

include even dead in
theorem table_exact : q=table ⟨(entries q).a,0,0,0,0,0,0,(entries q).x⟩ := by
  simp only [PaperTerminalBridgeSparseOrders.MiddleLive,not_or,not_not] at dead
  calc
    q=table (entries q):=(table_entries q even).symm
    _=table ⟨(entries q).a,0,0,0,0,0,0,(entries q).x⟩:=by
      congr 1
      apply Entries.ext <;> simp only [dead.1,dead.2.1,dead.2.2.1,
        dead.2.2.2.1,dead.2.2.2.2.1,dead.2.2.2.2.2]

include even dead in
theorem mapped (phi : K→+*AlgebraicComplex) (first : (entries q).a≠0) (last : (entries q).x≠0) :
    PureEquality (RingHomRealization.mapSignature phi q) := by
  refine ⟨phi (entries q).a,phi (entries q).x,(map_ne_zero phi).mpr first,
    (map_ne_zero phi).mpr last,?_⟩
  have form:=table_exact q even dead
  funext x
  change phi (q x)=_
  rw [congrFun form x]
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [table,ge4,complementWord,funext_iff,Fin.forall_fin_succ,h0,h1,h2,h3]

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperTerminalBridgeSparsePure
end
