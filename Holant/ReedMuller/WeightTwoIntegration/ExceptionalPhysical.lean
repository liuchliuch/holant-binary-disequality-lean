import Holant.ReedMuller.WeightTwoIntegration.ExceptionalLinks
import Holant.ReedMuller.WeightTwoIntegration.ExceptionalReconstruction

/-! The exceptional construction with actual fixed I/X binary resources.
Every native edge is X, and every resource scale is retained. -/
noncomputable section
namespace Holant.ReedMuller.WeightTwoIntegration
open scoped BigOperators
open CoefficientAtlas ExceptionalTopology
set_option backward.isDefEq.respectTransparency false

def actualKernel (minus : Bool) : Kernel ℂ :=
  if minus then Signature.disequality else Signature.equality

structure ExceptionalBinaries (family : SignatureFamily ℂ) where
  scale : Bool → ℂ
  nonzero : ∀ b, scale b ≠ 0
  available : ∀ b,
    (⟨2,fun x => scale b * actualKernel b (x 0) (x 1)⟩ : AnySignature ℂ) ∈ family

def chooseSign (s : ℂ) : Bool := if s = 1 then false else true

theorem chooseSign_value (s : ℂ) (hs : s = 1 ∨ s = -1) :
    (if chooseSign s then (-1 : ℂ) else 1) = s := by
  rcases hs with rfl | rfl <;> norm_num [chooseSign]

def linkSigns (d : ExceptionalData) : Fin 4 → Bool :=
  ![chooseSign d.eta,false,chooseSign d.theta,false]

def linkKernels {family : SignatureFamily ℂ} (d : ExceptionalData)
    (B : ExceptionalBinaries family) (e : Fin 4) : Kernel ℂ :=
  fun a b => B.scale (linkSigns d e) * actualKernel (linkSigns d e) a b

def physicalNetwork {family : SignatureFamily ℂ} (d : ExceptionalData)
    (B : ExceptionalBinaries family) (q : Signature ℂ 6) :
    FiniteNetwork ℂ (Bool ⊕ Fin 4) (Fin 4 × Bool) 4 :=
  ExceptionalLinks.subdivide (network q (fun _ => Signature.disequality)) (linkKernels d B)

def physicalScale {family : SignatureFamily ℂ} (d : ExceptionalData)
    (B : ExceptionalBinaries family) (c : ℂ) : ℂ :=
  16 * c^2 * ∏ e, B.scale (linkSigns d e)

theorem physicalScale_ne_zero {family : SignatureFamily ℂ} (d : ExceptionalData)
    (B : ExceptionalBinaries family) (c : ℂ) (hc : c ≠ 0) : physicalScale d B c ≠ 0 := by
  exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hc))
    (Finset.prod_ne_zero_iff.mpr fun e _ => B.nonzero _)

theorem sandwich_actualKernel (b : Bool) (c : ℂ) :
    Kernel.mul (Kernel.mul Signature.disequality (fun x y => c * actualKernel b x y))
      Signature.disequality = fun x y => c * actualKernel b x y := by
  funext x y
  cases b <;> cases x <;> cases y <;>
    simp [Kernel.mul,actualKernel,Signature.disequality,Signature.equality]

theorem pullback_actualKernel (b : Bool) :
    Kernel.pullback (actualKernel b) walshKernel =
      fun x y => 2 * diagonal (if b then -1 else 1) x y := by
  funext x y
  cases b <;> cases x <;> cases y <;>
    norm_num [Kernel.pullback,Kernel.mul,Kernel.transpose,actualKernel,walshKernel,
      diagonal,Signature.equality,Signature.disequality]

theorem pullback_linkSigns (d : ExceptionalData) (e : Fin 4) :
    Kernel.pullback (actualKernel (linkSigns d e)) walshKernel =
      fun x y => 2 * characters d.eta d.theta e x y := by
  rw [pullback_actualKernel]
  have hη := chooseSign_value d.eta d.eta_sign
  have hθ := chooseSign_value d.theta d.theta_sign
  fin_cases e <;> simp [linkSigns,characters,hη,hθ]

theorem network_scalars (q : Signature ℂ 6) (C : Fin 4 → Kernel ℂ)
    (c : ℂ) (s : Fin 4 → ℂ) :
    (network (fun x => c * q x) (fun e a b => s e * C e a b)).denote =
      fun x => (c^2 * ∏ e, s e) * (network q C).denote x := by
  classical
  let : DecidableEq (Fin 4) := Classical.decEq _
  funext x
  change (∑ z : Fin 4 × Bool → Bool,
    (∏ v : Bool, c * q (fun i : Fin 6 => Sum.elim x z (ports ⟨v,i⟩))) *
      ∏ e : Fin 4, s e * C e (z (e,false)) (z (e,true))) = _
  change _ = (c^2 * ∏ e, s e) * (∑ z : Fin 4 × Bool → Bool,
    (∏ v : Bool, q (fun i : Fin 6 => Sum.elim x z (ports ⟨v,i⟩))) *
      ∏ e : Fin 4, C e (z (e,false)) (z (e,true)))
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  simp only [Finset.prod_mul_distrib,Fintype.prod_bool]
  ring

/-- Exact physical denotation: two copies of q, four supplied link vertices,
eight native X edges, and the full product of representative scales. -/
theorem physicalNetwork_denote {family : SignatureFamily ℂ} (d : ExceptionalData)
    (B : ExceptionalBinaries family) (q : Signature ℂ 6) (c : ℂ)
    (hq : q = fun x => c * Signature.coordinateAction (fun _ => walshKernel) (paired d.h) x) :
    (physicalNetwork d B q).denote = fun x => physicalScale d B c *
      Signature.coordinateAction (fun _ => walshKernel) (pairedOutput d.Q) x := by
  rw [physicalNetwork,ExceptionalLinks.denote_subdivide]
  change (network q (fun e => Kernel.mul
    (Kernel.mul Signature.disequality (linkKernels d B e)) Signature.disequality)).denote = _
  have he : (fun e => Kernel.mul
      (Kernel.mul Signature.disequality (linkKernels d B e)) Signature.disequality) =
      linkKernels d B := by
    funext e
    exact sandwich_actualKernel (linkSigns d e) (B.scale (linkSigns d e))
  rw [he]
  change (network q (fun e x y => B.scale (linkSigns d e) * actualKernel (linkSigns d e) x y)).denote = _
  rw [hq,network_scalars]
  have ht := ExceptionalTransport.denote_action
    (network (paired d.h) (fun e => actualKernel (linkSigns d e))) walshKernel
  change (network (Signature.coordinateAction (fun _ => walshKernel) (paired d.h))
    (fun e => actualKernel (linkSigns d e))).denote =
    Signature.coordinateAction (fun _ => walshKernel)
      (network (paired d.h) (fun e => Kernel.pullback (actualKernel (linkSigns d e)) walshKernel)).denote at ht
  simp_rw [pullback_linkSigns] at ht
  have hs := network_scalars (paired d.h) (characters d.eta d.theta) 1 (fun _ => 2)
  simp only [one_mul,one_pow,Finset.prod_const,Finset.card_univ,Fintype.card_fin] at hs
  rw [hs,exceptional_logical_network,coordinateAction_scalar] at ht
  rw [ht]
  funext x
  simp only [physicalScale]
  ring

theorem physicalNetwork_realizes {family : SignatureFamily ℂ} (d : ExceptionalData)
    (B : ExceptionalBinaries family) (q : Signature ℂ 6)
    (hq : (⟨6,q⟩ : AnySignature ℂ) ∈ family) :
    Gadget.Realizes family .disequality (physicalNetwork d B q).denote := by
  apply ExceptionalLinks.realizes_subdivide
  · intro v
    exact hq
  · intro e
    exact B.available (linkSigns d e)

theorem physicalNetwork_vertices {family : SignatureFamily ℂ} (d : ExceptionalData)
    (B : ExceptionalBinaries family) (q : Signature ℂ 6) :
    (physicalNetwork d B q).toNetwork.shape.vertices = 6 := by
  simp [physicalNetwork,ExceptionalLinks.vertex_count]

theorem physicalNetwork_edges {family : SignatureFamily ℂ} (d : ExceptionalData)
    (B : ExceptionalBinaries family) (q : Signature ℂ 6) :
    (physicalNetwork d B q).toNetwork.shape.edges = 8 := by
  simp [physicalNetwork,ExceptionalLinks.edge_count]

end Holant.ReedMuller.WeightTwoIntegration
