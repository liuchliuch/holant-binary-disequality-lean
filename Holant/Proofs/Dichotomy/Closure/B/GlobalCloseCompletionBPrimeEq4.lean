import Holant.Proofs.Dichotomy.Closure.Affine.GlobalCloseCompletionAffineAncestorEq4

/-! A labelled prime complementary EO graph in either literal Affine or
Product has an actual scalar-Eq4 output. This generic algebraic source theorem
is usable after the genuine B-coordinate native source, without requiring a
transformed saturation palette or a new complete-group assumption. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionBPrimeEq4
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity FixedGadgetSubstitution
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.Certificates.EqualityQuaternary
open Holant.LocalDrafts.Hardness.EightVertexNonexception
open StableCurrentEvenEOTract
namespace E
export GlobalCloseCompletionSparseEq4Flip (identity leg legLabels leg_exact leg_native equality_denote)
end E
namespace P
export GlobalCloseCompletionProductAncestorSupport (prime_product_support_pair prime_not_singleton)
end P
namespace A
export GeneralEOAffineNetworkChain (network labels exact native power_denote)
end A
namespace B
export EOBinaryPlaneCore (compress normalized normalized_lift)
end B
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {a : ℕ → ℕ}
variable (H : (i : Fin s) → Signature AlgebraicComplex (a i.val))
variable (j : Fin s) (identity : (⟨a j.val,H j⟩ : AnySignature AlgebraicComplex)=⟨2,E.identity⟩)

structure Output : Type where
  network : Network AlgebraicComplex 4
  labels : Labelling network.shape s 1 a
  exact : LabelledNetwork.Exact H network labels
  native : ∀e,network.edge e=Signature.disequality
  scalar : AlgebraicComplex
  nonzero : scalar≠0
  denote : network.denote=scalar • Holant.EightVertex.ProductAnchor.equalityFour

def fromDEQ (D : GeneralEODEQProducerNormalize.Produced H) : Output H := by
  let L := E.legLabels D.network D.labels j (congrArg Sigma.fst identity) false
  have hL := E.leg_exact H D.network D.labels D.exact j identity false
  exact ⟨E.leg (E.leg D.network false) true,
    E.legLabels (E.leg D.network false) L j (congrArg Sigma.fst identity) true,
    E.leg_exact H (E.leg D.network false) L hL j identity true,
    E.leg_native (E.leg D.network false) (E.leg_native D.network D.native false) true,
    D.scalar,D.nonzero,E.equality_denote D.network D.scalar D.denote⟩

variable (M : Network AlgebraicComplex 4) (L : Labelling M.shape s 1 a)
variable (literal : LabelledNetwork.Exact H M L) (native : ∀e,M.edge e=Signature.disequality)
variable (eo : DenseEOUnitLocal.EOSupport M.denote) (prime : TensorPrime M.denote)
variable (closed : ∀x,M.denote (complementWord x)=0 ↔ M.denote x=0)

include prime in
theorem product_pair (product : Product M.denote) : Nonempty (GeneralEODEQProducerCore.Pair M.denote) := by
  have hp := (PrimalityInterfaces.retained_equality_prime M.denote).mpr prime
  obtain ⟨w,support⟩ := P.prime_product_support_pair M.denote (by decide) hp product
  have left : M.denote w≠0 := by
    intro zero
    apply P.prime_not_singleton M.denote (by decide) hp (fun i => !(w i))
    intro x hx
    exact (support x hx).resolve_left (fun h => hx (h ▸ zero))
  have right : M.denote (fun i => !(w i))≠0 := by
    intro zero
    apply P.prime_not_singleton M.denote (by decide) hp w
    intro x hx
    exact (support x hx).resolve_right (fun h => hx (h ▸ zero))
  exact ⟨⟨w,(fun i => !(w i)),left,right,
    le_of_eq ((GeneralEODEQProducerCore.distance_eq_iff w (fun i => !(w i))).mpr
      (by intro i; cases w i <;> decide)).symm,fun x hx _ => support x hx⟩⟩

include literal native eo prime identity in
theorem product_output (product : Product M.denote) : Nonempty (Output H) := by
  obtain ⟨pair⟩ := product_pair M prime product
  have central : Signature.CentralSupport M.denote := by
    intro x hx
    exact eo x (by change 2*weight x≠4 at hx; omega)
  let R : GeneralEODEQProducerReduction.Reduced H := ⟨M,L,literal,native,central,pair⟩
  obtain ⟨D⟩ := GeneralEODEQProducerNormalize.produce_reduced H R
  exact ⟨fromDEQ H j identity D⟩

include literal native eo prime closed identity in
theorem affine_output (affine : Affine M.denote) : Nonempty (Output H) := by
  classical
  by_cases product : Product M.denote
  · exact product_output H j identity M L literal native eo prime product
  obtain ⟨i,zero⟩ := missing_middle_of_supports M.denote eo .positive
    (fun x y z hx hy hz => Or.inl (affine_support_xor3 affine x y z hx hy hz))
  have opposite : FiveSupportEOOrdering.middleCoeff M.denote (5-i)=0 := by
    rw [FiveSupportEOOrdering.middleCoeff,←middleWord_complement]
    exact (closed (FiveSupportEOOrdering.middleWord i)).mpr zero
  let e := FiveSupportEOOrdering.orderAt i
  let f := B.compress (B.normalized M.denote i)
  have plane : EOBinaryPlaneCore.lift f=Tensor.reindex e M.denote :=
    B.normalized_lift M.denote eo i zero opposite
  have fa : Affine f := by
    have h := affine.precompose (EOBinaryPlaneTract.transportPairing e EOBinaryPlaneCore.pairing).word
      (EOBinaryPlaneTract.pairing_affine _)
    change Affine ((EOBinaryPlaneTract.transportPairing e EOBinaryPlaneCore.pairing).restrict M.denote) at h
    rw [EOBinaryPlaneTract.restriction_reindex,EOBinaryPlaneCore.restrict_eq] at h
    exact h
  have fp : ¬Product f := by
    intro hp
    have h := EOBinaryPlaneTract.product_lift hp
    rw [plane] at h
    exact product (EOBinaryPlaneTract.product_unreindex e M.denote h)
  have full := GlobalCloseCompletionAffineAncestorEq4.binary_full f fa fp
  let c := GeneralEOAffinePlanePeriod.scale f
  have cn : c≠0 := GeneralEOAffinePlanePeriod.scale_ne_zero f full
  have power : GeneralEOAffinePlaneChain.table f^24=c •
      (1 : GeneralEOAffinePlaneChain.Mat (K:=AlgebraicComplex)) :=
    GeneralEOAffinePlanePeriod.power f full fa fp
  let D : GeneralEODEQProducerNormalize.Produced H :=
    ⟨A.network M e 23,A.labels M L e 23,A.exact M L e H literal 23,
      A.native M e native 23,c,cn,A.power_denote M e f plane.symm 23 c power⟩
  exact ⟨fromDEQ H j identity D⟩

include literal native eo prime closed identity in
theorem class_output (C : EOClass) (member : C.Holds M.denote) : Nonempty (Output H) := by
  cases C with
  | affine => exact affine_output H j identity M L literal native eo prime closed member
  | product => exact product_output H j identity M L literal native eo prime member

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionBPrimeEq4
end
