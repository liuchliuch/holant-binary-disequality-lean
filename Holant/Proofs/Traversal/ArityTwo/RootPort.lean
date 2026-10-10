import Holant.Proofs.Traversal.ArityTwo.RawBytecodeMachine


namespace Holant.LocalDrafts.TraversalCompletion.ArityTwo.RootPort
open Holant Holant.Complexity Computability
open GraphPreprocessing GraphPreprocessing.OriginalCoefficient
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {s b : ℕ} {arity : ℕ → ℕ}
variable (x : RawRootReach.Input s b arity)

def first (hp : 0 < PortWalk.degree (arity := arity) x.1.val x.2) : x.1.val.Ports arity := ⟨x.2,⟨0,hp⟩⟩

theorem stored (hp : 0 < PortWalk.degree (arity := arity) x.1.val x.2) :
    RawBytecodeMachine.firstEndpoint s b arity x = x.1.val.portEndpoint x.1.property (first x hp) := by
  have hl := (x.1.property.1 x.2).2
  have hzero : 0 < (x.1.val.vertices.get x.2).2.length := by
    change 0 < arity (x.1.val.vertices.get x.2).1 at hp
    omega
  change (x.1.val.vertices.get x.2).2.getD 0 (0,false) =
    (x.1.val.vertices.get x.2).2[0]'hzero
  exact List.getD_eq_getElem _ _ hzero

def query (hp : 0 < PortWalk.degree (arity := arity) x.1.val x.2) (opposite : Bool) : RawPortQuery.Input s b arity :=
  ActionTableMeaning.query x.1.val x.1.property
    (if opposite then PortWalk.cross x.1.val x.1.property (first x hp) else first x hp)

theorem prepared (hp : 0 < PortWalk.degree (arity := arity) x.1.val x.2) (opposite : Bool) :
    RawBytecodeMachine.endpointWord s b arity opposite x =
      (RawPortQuery.encoding s b arity).encode (query x hp opposite) := by
  rw [RawBytecodeMachine.endpointWord,stored x hp]
  have hc : x.1.val.portEndpoint x.1.property (PortWalk.cross x.1.val x.1.property (first x hp)) =
      ((x.1.val.portEndpoint x.1.property (first x hp)).1,
        !(x.1.val.portEndpoint x.1.property (first x hp)).2) := by
    have he := congrArg (fun q : Fin x.1.val.edges.length × Bool => (q.1.val,q.2))
      (PortWalk.route_cross x.1.val x.1.property (first x hp))
    exact he
  cases opposite <;>
    simp [query,ActionTableMeaning.query,RawPortQuery.encoding,EndpointVertex.input_word,
      RawClosedNetwork.route,hc]

end
end Holant.LocalDrafts.TraversalCompletion.ArityTwo.RootPort
