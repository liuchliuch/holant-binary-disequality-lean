import Holant.Proofs.Dichotomy.Closure.A0.GlobalCloseCompletionA0KernelRealizes
import Holant.Marked.Fusion
import Holant.Proofs.Closure.ClosurePhysicalBridgeHolographicOpenAlgebra
import Holant.NetworkAlgebra

/-! Open coordinate transport using one actual original binary to implement
the transformed edge. The boundary action and every uniform edge multiplier
are explicit. This is a genuine gadget theorem, separate from closed oracle
value reductions, and uses only current strict network interfaces. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionA0OpenCoordinate
open Holant Holant.Tractable Holant.Marked
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.OpenNetworkComposition
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false

theorem upTo_scale {K : Type*} [Field K] {n : ℕ} (F : SignatureFamily K)
    (f : Signature K n) (h : Gadget.RealizesUpTo F .disequality f) (c : K) (hc : c≠0) :
    Gadget.RealizesUpTo F .disequality (fun x => c*f x) := by
  obtain ⟨a,ha,hf⟩ := h
  refine ⟨a/c,div_ne_zero ha hc,?_⟩
  convert hf using 1
  funext x
  field_simp

variable (F : SignatureFamily AlgebraicComplex) (hI : RetainsIdentity F)
variable (B : Binary (K:=AlgebraicComplex))
variable (hB : Gadget.Realizes F .disequality (Holant.Projective.BoundedTorsion.binarySignature B))
variable (U : InvertibleKernel) (c : AlgebraicComplex) (hc : c≠0)
variable (edge : Kernel.pullback Signature.disequality U.inverse=
  scale c (GlobalCloseCompletionA0KernelRealizes.edge B))
variable {n : ℕ} (N : Network AlgebraicComplex n)
variable (native : ∀e,N.edge e=Signature.disequality)
variable (vertex : ∀v,Gadget.RealizesUpTo F .disequality (U.action (N.vertex v)))

private def restored : Network AlgebraicComplex n where
  shape := N.shape
  vertex v := U.action (N.vertex v)
  edge _ := GlobalCloseCompletionA0KernelRealizes.edge B

include edge native in
private theorem scaled_graph : (restored B U N).scaleEdges (fun _ => c)=
    OpenHolographic.transform N U.inverse U.matrix := by
  unfold restored Network.scaleEdges OpenHolographic.transform
  congr 1
  funext e
  rw [native e,edge]
  rfl

include hc edge native vertex hI hB in
theorem network_coordinate : Gadget.RealizesUpTo F .disequality (U.action N.denote) := by
  have realized := GlobalCloseCompletionA0KernelRealizes.network_upTo B F hI hB
    (restored B U N) vertex (fun _ => rfl)
  have scaleNonzero : (∏ _e : Fin N.shape.edges,c)≠0 := by
    apply Finset.prod_ne_zero_iff.mpr
    exact fun _ _ => hc
  have scaled := upTo_scale F (restored B U N).denote realized (∏ _e : Fin N.shape.edges,c) scaleNonzero
  have den : (fun x => (∏ _e : Fin N.shape.edges,c)*(restored B U N).denote x)=U.action N.denote := by
    calc
      _ = ((restored B U N).scaleEdges (fun _ => c)).denote :=
        funext (fun x => (Network.denote_scaleEdges (restored B U N) (fun _ => c) x).symm)
      _ = (OpenHolographic.transform N U.inverse U.matrix).denote := by rw [scaled_graph B U c edge N native]
      _ = U.action N.denote := OpenHolographic.denote_transform N U.inverse U.matrix U.inverse_matrix
  rwa [den] at scaled

variable (H : SignatureFamily AlgebraicComplex) (hH : RetainsIdentity H)
variable (members : ∀f∈H,Gadget.RealizesUpTo F .disequality (U.action f.2))

include hc edge hI hB hH members in
theorem coordinate {n : ℕ} (f : Signature AlgebraicComplex n) (actual : Gadget.Realizes H .disequality f) :
    Gadget.RealizesUpTo F .disequality (U.action f) := by
  obtain ⟨N,labels,native,denote⟩ := OrdinaryNormalization.realizes_exists_ordinary hH actual
  rw [←denote]
  exact network_coordinate F hI B hB U c hc edge N native (fun v => members _ (labels v))

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionA0OpenCoordinate
end
