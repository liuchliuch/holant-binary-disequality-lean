import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPureCompressionValue
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPureMergeSynthesis
import Holant.Proofs.Dichotomy.WithoutIdentity.NoINativeOpenSubstitution

/-! Original-labelled signed compression with the exact original coefficient
field, exact scalar one, and the interleaved opposite-pair boundary. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureCompressionSource
open Holant Holant.Complexity
namespace G
export NoIPureCompressionGraph (Fixed Fiber Vertices arity mask fixedSign vertex finite column signedWord)
end G
namespace M
export NoIPureMergeSynthesis (produce value)
end M
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 900000
set_option Elab.async false
variable {K : Type} [Field K] [Algebra ℚ K] {s n m : ℕ} {a : ℕ → ℕ}
variable (H : (i : Fin s) → Signature K (a i.val))
variable (Q : NativeAntiTargetSource.Output H 4) (X : NativeAntiTargetSource.Output H 2)
variable (pins : Bool → NativeAntiTargetSource.Output H 1)
variable (qform : Q.network.denote = Holant.EightVertex.ProductAnchor.equalityFour)
variable (xform : X.network.denote = fun x => Signature.disequality (x 0) (x 1))
variable (pinform : ∀ b, (pins b).network.denote = fun x => if x 0 = b then 1 else 0)
variable (N : NativeAntiTargetSource.Output H n)
variable (base : Fin n → Bool) (p : Fin n → Bool ⊕ Fin m)
variable (legal : ∀ j, G.column base p j % 4 = 0)

include legal in
theorem maskLegal (j : Fin m) : NoIPureMergeWords.Legal (G.mask base p j) := by
  rw [NoIPureMergeWords.Legal,NoIPureCompressionGraph.mask_charge]
  exact legal j

def graph : (v : G.Vertices p) → NativeAntiTargetSource.Output H (G.arity p v)
  | .inl _ => N
  | .inr (.inl i) => pins (!(G.fixedSign base p i))
  | .inr (.inr j) => M.produce H Q X qform xform
      (n:=2+Fintype.card (G.Fiber p j)) (by omega) (G.mask base p j)
      (maskLegal base p legal j)

include pinform in
theorem graph_value (v : G.Vertices p) :
    (graph H Q X pins qform xform N base p legal v).network.denote = G.vertex N.network.denote base p v := by
  rcases v with _ | i | j
  · rfl
  · exact pinform _
  · exact M.value H Q X qform xform (by omega) (G.mask base p j) (maskLegal base p legal j)

abbrev outer := (G.finite N.network.denote base p).toNetwork

def replacement (v : Fin (outer H N base p).shape.vertices) :
    NativeAntiTargetSource.Output H ((outer H N base p).shape.arity v) :=
  graph H Q X pins qform xform N base p legal ((Fintype.equivFin (G.Vertices p)).symm v)

def output : NativeAntiTargetSource.Output H (m*2) :=
  NoINativeOpenSubstitution.output H (outer H N base p)
    (replacement H Q X pins qform xform N base p legal) (fun _ => rfl)

include pinform in
theorem value : (output H Q X pins qform xform N base p legal).network.denote =
    NoIPurePairedHardForm.paired (fun z => N.network.denote (G.signedWord base p z)) := by
  rw [output,NoINativeOpenSubstitution.value]
  · rw [outer,FiniteNetwork.denote_toNetwork]
    exact NoIPureCompressionValue.value N.network.denote base p
  · intro v
    exact graph_value H Q X pins qform xform pinform N base p legal _

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureCompressionSource
end
