import Holant.Proofs.Reductions.GeneralExtraction.GeneralPowerExposure
import Holant.Complexity.BinaryInterpolation.Chains.Template

/-! Genuine finite source-label transport and target-scalar correction for a
saved actual power macro. The actual network and exponent are unchanged;
label transport consumes literal table equality, and the correction scalar
stays in the SAME given field. No target compiler or new realization is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ProgrammePowerTransport
open Holant Holant.Complexity
open Holant.LocalDrafts.Hardness.GeneralExtraction
open Holant.Complexity.FixedGadgetSubstitution
variable {K : Type} [Field K] {s t n : ℕ} {a b : ℕ → ℕ}
variable (G : (i : Fin s) → Signature K (a i.val))
variable (H : (i : Fin t) → Signature K (b i.val))
variable (index : Fin s → Fin t)
variable (tables : ∀ i, (⟨b (index i).val,H (index i)⟩ : AnySignature K) = ⟨a i.val,G i⟩)
variable {f : Signature K n} (M : GeneralPowerExposure.PowerMacro G f)

def arityIdentity (i : Fin s) : b (index i).val = a i.val := congrArg Sigma.fst (tables i)

/-- The finite label map relabels THIS saved network, preserving every actual
vertex and edge occurrence, full exponent and original scalar correction. -/
def relabel : GeneralPowerExposure.PowerMacro H f := by
  let lab : Labelling M.network.shape t 1 b := {
    vertex := fun v => index (M.labels.vertex v)
    vertex_arity := fun v => (arityIdentity G H index tables (M.labels.vertex v)).trans (M.labels.vertex_arity v)
    edge := M.labels.edge }
  refine ⟨M.exponent,M.positive,M.scale,M.scale_ne_zero,M.network,lab,?_⟩
  rw [Labelling.denote_template]
  have hM := M.value
  rw [Labelling.denote_template] at hM
  rw [←hM]
  apply Network.denote_congr
  · intro v x
    have hs := Holant.Complexity.BinaryInterpolation.Chains.signature_cast_apply
      (H (index (M.labels.vertex v))) (G (M.labels.vertex v))
      (tables (M.labels.vertex v)) (arityIdentity G H index tables (M.labels.vertex v))
      (fun i => x (Fin.cast (M.labels.vertex_arity v) i))
    simpa only [Labelling.sourceNetwork,lab,Fin.cast_cast] using hs
  · intro e x y
    rfl

@[simp] theorem relabel_network : (relabel G H index tables M).network = M.network := rfl
@[simp] theorem relabel_exponent : (relabel G H index tables M).exponent = M.exponent := rfl
@[simp] theorem relabel_scale : (relabel G H index tables M).scale = M.scale := rfl
@[simp] theorem relabel_vertex (v : Fin M.network.shape.vertices) :
    (relabel G H index tables M).labels.vertex v = index (M.labels.vertex v) := rfl

/-- Target scaling is counted once for each ACTUAL macro copy. -/
theorem blockPower_scale (f : Signature K n) (c : K) (e : ℕ) :
    Carrier.blockPower (c • f) e = (fun x => c^e * Carrier.blockPower f e x) := by
  funext x
  simp [Carrier.blockPower,Pi.smul_apply,smul_eq_mul,Finset.prod_mul_distrib]

variable (c : K) (hc : c ≠ 0) {fNew : Signature K n} (target : fNew = c • f)

/-- Reuse the same actual macro for the scaled target. Only its ORIGINAL-field
nonzero correction changes, from M.scale to M.scale/c^M.exponent. -/
def scaleTarget : GeneralPowerExposure.PowerMacro G fNew := by
  refine ⟨M.exponent,M.positive,M.scale / c^M.exponent,
    div_ne_zero M.scale_ne_zero (pow_ne_zero _ hc),M.network,M.labels,?_⟩
  rw [M.value,target,blockPower_scale]
  funext x
  change M.scale * Carrier.blockPower f M.exponent x =
    (M.scale / c^M.exponent) * (c^M.exponent * Carrier.blockPower f M.exponent x)
  rw [←mul_assoc,div_mul_cancel₀ _ (pow_ne_zero _ hc)]

@[simp] theorem scaleTarget_network : (scaleTarget G M c hc target).network = M.network := rfl
@[simp] theorem scaleTarget_labels : (scaleTarget G M c hc target).labels = M.labels := rfl
@[simp] theorem scaleTarget_exponent : (scaleTarget G M c hc target).exponent = M.exponent := rfl
@[simp] theorem scaleTarget_scale : (scaleTarget G M c hc target).scale = M.scale / c^M.exponent := rfl

/-- The joint operation consumes the actual saved macro, literal copied source
labels and original-field scalar/value transport, never a completion callback. -/
def transport : GeneralPowerExposure.PowerMacro H fNew :=
  scaleTarget H (relabel G H index tables M) c hc target

@[simp] theorem transport_network : (transport G H index tables M c hc target).network = M.network := rfl
@[simp] theorem transport_exponent : (transport G H index tables M c hc target).exponent = M.exponent := rfl
@[simp] theorem transport_scale : (transport G H index tables M c hc target).scale = M.scale / c^M.exponent := rfl
@[simp] theorem transport_vertex (v : Fin M.network.shape.vertices) :
    (transport G H index tables M c hc target).labels.vertex v = index (M.labels.vertex v) := rfl
end Holant.LocalDrafts.RemoteWork.StableClosureV2.ProgrammePowerTransport
