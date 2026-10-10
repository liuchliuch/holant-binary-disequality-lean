import Holant.Proofs.Dichotomy.Closure.B.GlobalCloseCompletionBEqualityRealizes
import Holant.Proofs.Closure.ClosurePhysicalBridgeHolographicOpenAlgebra
import Holant.Proofs.Closure.ClosureBStableMatrix
import Holant.NetworkAlgebra

/-! Projective realization in both directions for the genuine B-coordinate
native alphabet. Open boundary actions and every uniform edge multiplier are
kept; equality closures are implemented using actual retained I. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionBCoordinateRealizes
open Holant Holant.Tractable Holant.Marked
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.OpenNetworkComposition
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false

private theorem upTo_scale {K : Type*} [Field K] {n : ℕ} (F : SignatureFamily K)
    (f : Signature K n) (h : Gadget.RealizesUpTo F .disequality f) (c : K) (hc : c≠0) :
    Gadget.RealizesUpTo F .disequality (fun x => c*f x) := by
  obtain ⟨a,ha,hf⟩ := h
  refine ⟨a/c,div_ne_zero ha hc,?_⟩
  convert hf using 1
  funext x
  field_simp

section Generic
variable (F : SignatureFamily AlgebraicComplex) (hI : RetainsIdentity F)
variable (U : InvertibleKernel) (c : AlgebraicComplex) (hc : c≠0)
variable (edge : Kernel.pullback Signature.disequality U.inverse=scale c Signature.equality)
variable {n : ℕ} (N : Network AlgebraicComplex n)
variable (native : ∀e,N.edge e=Signature.disequality)
variable (vertex : ∀v,Gadget.RealizesUpTo F .disequality (U.action (N.vertex v)))

private def ordinary : Network AlgebraicComplex n where
  shape := N.shape
  vertex v := U.action (N.vertex v)
  edge _ := Signature.equality

include edge native in
private theorem scaled_graph : (ordinary U N).scaleEdges (fun _ => c)=
    OpenHolographic.transform N U.inverse U.matrix := by
  unfold ordinary Network.scaleEdges OpenHolographic.transform
  congr 1
  funext e
  rw [native e,edge]
  rfl

include hc edge native vertex hI in
theorem network_coordinate : Gadget.RealizesUpTo F .disequality (U.action N.denote) := by
  have realized := GlobalCloseCompletionBEqualityRealizes.network_upTo F hI
    (ordinary U N) vertex (fun _ => rfl)
  have scaleNonzero : (∏ _e : Fin N.shape.edges,c)≠0 := by
    apply Finset.prod_ne_zero_iff.mpr
    exact fun _ _ => hc
  have scaled := upTo_scale F (ordinary U N).denote realized (∏ _e : Fin N.shape.edges,c) scaleNonzero
  have den : (fun x => (∏ _e : Fin N.shape.edges,c)*(ordinary U N).denote x)=U.action N.denote := by
    calc
      _ = ((ordinary U N).scaleEdges (fun _ => c)).denote :=
        funext (fun x => (Network.denote_scaleEdges (ordinary U N) (fun _ => c) x).symm)
      _ = (OpenHolographic.transform N U.inverse U.matrix).denote := by rw [scaled_graph U c edge N native]
      _ = U.action N.denote := OpenHolographic.denote_transform N U.inverse U.matrix U.inverse_matrix
  rwa [den] at scaled

variable (H : SignatureFamily AlgebraicComplex) (hH : RetainsIdentity H)
variable (members : ∀f∈H,Gadget.RealizesUpTo F .disequality (U.action f.2))

include hc edge hI hH members in
theorem coordinate {n : ℕ} (f : Signature AlgebraicComplex n) (actual : Gadget.Realizes H .disequality f) :
    Gadget.RealizesUpTo F .disequality (U.action f) := by
  obtain ⟨N,labels,native,denote⟩ := OrdinaryNormalization.realizes_exists_ordinary hH actual
  rw [←denote]
  exact network_coordinate F hI U c hc edge N native (fun v => members _ (labels v))
end Generic

def family (F : SignatureFamily AlgebraicComplex) : SignatureFamily AlgebraicComplex :=
  familyAction basisB.symm F ∪ {(⟨2,kernelSignature Signature.equality⟩ : AnySignature AlgebraicComplex)}

theorem identity (F : SignatureFamily AlgebraicComplex) : RetainsIdentity (family F) := Or.inr rfl

theorem forward_identity : basisB.action (kernelSignature Signature.equality)=
    fun x => (-2*imaginaryUnit)*kernelSignature Signature.disequality x := by
  rw [InvertibleKernel.action,coordinateAction_kernelSignature]
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;>
    simp [kernelSignature,basisB,UB,Kernel.mul_apply,Kernel.transpose,Signature.equality,Signature.disequality,h0,h1] <;>
    ring_nf <;> norm_num [imaginaryUnit_sq]

theorem restored_member (F : SignatureFamily AlgebraicComplex) (f : AnySignature AlgebraicComplex)
    (member : f∈family F) : Gadget.RealizesUpTo F .disequality (basisB.action f.2) := by
  rcases member with ⟨g,hg,rfl⟩ | equality
  · rw [basisB.action_symm_action]
    exact ⟨1,one_ne_zero,by simpa only [one_mul] using Gadget.realizes_of_mem F .disequality g.2 hg⟩
  · change f=(⟨2,kernelSignature Signature.equality⟩ : AnySignature AlgebraicComplex) at equality
    subst f
    rw [forward_identity]
    have actual : Gadget.Realizes F .disequality (kernelSignature Signature.disequality) :=
      @Gadget.realizes_edgeBox AlgebraicComplex
        (inferInstance : Field AlgebraicComplex).toSemifield.toCommSemiring F .disequality
    exact upTo_scale F (kernelSignature Signature.disequality)
      ⟨1,one_ne_zero,by simpa only [one_mul] using actual⟩
      (-2*imaginaryUnit) edgeB_multiplier_ne_zero

private theorem inverse_edge : Kernel.pullback Signature.disequality basisB.inverse=
    scale (imaginaryUnit/2) Signature.equality := by
  funext b c
  cases b <;> cases c <;>
    simp [Kernel.pullback,basisB,UBInv,Kernel.mul_apply,Kernel.transpose,
      Signature.equality,Signature.disequality,scale] <;>
    ring_nf <;> norm_num [imaginaryUnit_sq]

/-- Every normalized native gadget has a real projective original-P graph;
new normalized identity vertices and original edge scalars are accounted for. -/
theorem backward (F : SignatureFamily AlgebraicComplex) (hI : RetainsIdentity F)
    {n : ℕ} (f : Signature AlgebraicComplex n) (actual : Gadget.Realizes (family F) .disequality f) :
    Gadget.RealizesUpTo F .disequality (basisB.action f) :=
  coordinate F hI basisB (imaginaryUnit/2)
    (div_ne_zero imaginaryUnit_ne_zero (by norm_num)) inverse_edge
    (family F) (identity F) (restored_member F) f actual

/-- The converse is also constructive; no transformed original binary is
claimed exact when its actual graph still has a nonzero multiplier. -/
theorem forward (F : SignatureFamily AlgebraicComplex) (hI : RetainsIdentity F)
    {n : ℕ} (f : Signature AlgebraicComplex n) (actual : Gadget.Realizes F .disequality f) :
    Gadget.RealizesUpTo (family F) .disequality (basisB.symm.action f) := by
  apply coordinate (family F) (identity F) basisB.symm (-2*imaginaryUnit)
    edgeB_multiplier_ne_zero edgeB F hI ?_ f actual
  intro g hg
  exact ⟨1,one_ne_zero,by simpa only [one_mul] using
    Gadget.realizes_of_mem (family F) .disequality (basisB.symm.action g.2) (Or.inl ⟨g,hg,rfl⟩)⟩


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionBCoordinateRealizes
end
