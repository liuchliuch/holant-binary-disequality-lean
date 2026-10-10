import Holant.Proofs.Dichotomy.WithoutIdentity.NoINativeOpenSubstitutionSemantics
import Holant.Proofs.Dichotomy.Native.NativeAntiTargetOutput

/-! Actual original-labelled native substitution with an arbitrary boundary. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoINativeOpenSubstitution
open Holant Holant.Complexity
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open scoped BigOperators
namespace S
export NoINativeOpenSubstitutionSemantics (network Vertices Edges denote denote_scaled)
end S
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option Elab.async false
variable {K : Type} [Field K] [Algebra ℚ K] {s m : ℕ} {a : ℕ → ℕ}
variable (H : (i : Fin s) → Signature K (a i.val))
variable (N : Network K m)
variable (G : (v : Fin N.shape.vertices) → NativeAntiTargetSource.Output H (N.shape.arity v))
abbrev localNetworks := fun v => (G v).network
abbrev network := (S.network N (localNetworks H N G)).toNetwork

def labels : FixedGadgetSubstitution.Labelling (network H N G).shape s 1 a where
  vertex v :=
    let w := (Fintype.equivFin (S.Vertices N (localNetworks H N G))).symm v
    (G w.1).labels.vertex w.2
  vertex_arity v := by
    exact (G ((Fintype.equivFin (S.Vertices N (localNetworks H N G))).symm v).1).labels.vertex_arity _
  edge _ := 0

def output (native : ∀ e, N.edge e = Signature.disequality) :
    NativeAntiTargetSource.Output H m where
  network := network H N G
  labels := labels H N G
  exact v := by
    exact (G ((Fintype.equivFin (S.Vertices N (localNetworks H N G))).symm v).1).exact _
  native e := by
    change (S.network N (localNetworks H N G)).edge
      ((Fintype.equivFin (S.Edges N (localNetworks H N G))).symm e) = _
    cases (Fintype.equivFin (S.Edges N (localNetworks H N G))).symm e with
    | inl e => exact native e
    | inr e => exact (G e.1).native e.2

theorem value (native : ∀ e, N.edge e = Signature.disequality)
    (form : ∀ v, (G v).network.denote = N.vertex v) :
    (output H N G native).network.denote = N.denote := by
  change (S.network N (localNetworks H N G)).toNetwork.denote = _
  rw [FiniteNetwork.denote_toNetwork]
  funext x
  rw [S.denote]
  have h : (fun v => (G v).network.denote) = N.vertex := funext form
  change (Network.mk N.shape (fun v => (G v).network.denote) N.edge).denote x = _
  rw [h]

theorem value_scaled (native : ∀ e, N.edge e = Signature.disequality)
    (c : Fin N.shape.vertices → K)
    (form : ∀ v, (G v).network.denote = c v • N.vertex v) :
    (output H N G native).network.denote = (∏ v, c v) • N.denote := by
  change (S.network N (localNetworks H N G)).toNetwork.denote = _
  rw [FiniteNetwork.denote_toNetwork]
  funext x
  exact S.denote_scaled N (localNetworks H N G) x c form


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoINativeOpenSubstitution
end
