import Holant.Proofs.Closure.FrontierCurrentClosure
import Holant.Tractable.AffineOperations
import Holant.Proofs.FiniteGroups.Stabilization.FactorBaseChange

/-! Concrete proper-split reconstruction for the actual affine, product and
local-affine target classes, after the SAME shared inverse-basis action.
Local leaf membership and the transformed equality-edge condition remain
explicit. These are semantic closure identities, not evaluators or classifiers. -/
noncomputable section
set_option maxHeartbeats 0
set_option synthInstance.maxHeartbeats 0
set_option maxRecDepth 100000
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.FrontierSplitClosure
open Holant Holant.Algebraic Holant.Tractable
open Holant.LocalDrafts.FinitePGL2.Stabilization
open FrontierClosure FrontierCommonPresentation CurrentFrontierClosure

/-- Remap the same designated product factors along an actual coordinate map.
The nonzero unary witnesses, repeated factors and exact scalar are retained. -/
def remapFactor {m n : ℕ} (indices : Fin n → Fin m) : ProductFactor n → ProductFactor m
  | .unary j values hn => .unary (indices j) values hn
  | .equality j k => .equality (indices j) (indices k)
  | .disequality j k => .disequality (indices j) (indices k)

theorem remapFactor_eval {m n : ℕ} (indices : Fin n → Fin m) (h : ProductFactor n)
    (x : Fin m → Bool) : (remapFactor indices h).eval x = h.eval (fun j => x (indices j)) := by
  cases h <;> rfl

theorem product_coordinates {m n : ℕ} {f : Signature AlgebraicComplex n}
    (hf : Product f) (indices : Fin n → Fin m) : Product (fun x => f (fun j => x (indices j))) := by
  rcases hf with rfl | ⟨scale, hn, factors, rfl⟩
  · exact product_zero m
  · refine .inr ⟨scale, hn, factors.map (remapFactor indices), ?_⟩
    funext x
    simp only [productFormula, List.map_map, Function.comp_def, remapFactor_eval]

/-- Affine disjoint reconstruction uses the proved coordinate pullbacks,
actual support intersection and quadratic-phase multiplication. -/
theorem affine_disjoint {m n k : ℕ} (ports : (Fin m ⊕ Fin n) ≃ Fin k)
    {f : Signature AlgebraicComplex m} {g : Signature AlgebraicComplex n}
    (hf : Affine f) (hg : Affine g) : Affine (Tensor.reindex ports (Tensor.tensor f g)) :=
  (hf.precompose _ (coordinates_isAffineMap (fun j => ports (.inl j)))).mul
    (hg.precompose _ (coordinates_isAffineMap (fun j => ports (.inr j))))

theorem product_disjoint {m n k : ℕ} (ports : (Fin m ⊕ Fin n) ≃ Fin k)
    {f : Signature AlgebraicComplex m} {g : Signature AlgebraicComplex n}
    (hf : Product f) (hg : Product g) : Product (Tensor.reindex ports (Tensor.tensor f g)) :=
  (product_coordinates hf (fun j => ports (.inl j))).mul
    (product_coordinates hg (fun j => ports (.inr j)))

/-- Generic independent ordered port actions distribute over a disjoint tensor.
This is the same finite-sum identity used by the frozen primality interfaces,
without their specialization to complex coefficients or four ports. -/
def splitWords {m n k : ℕ} (ports : (Fin m ⊕ Fin n) ≃ Fin k) :
    (Fin k → Bool) ≃ ((Fin m → Bool) × (Fin n → Bool)) :=
  (Equiv.arrowCongr ports.symm (Equiv.refl Bool)).trans
    (Equiv.sumArrowEquivProdArrow (Fin m) (Fin n) Bool)

theorem action_disjoint {K : Type*} [CommSemiring K] {m n k : ℕ}
    (ports : (Fin m ⊕ Fin n) ≃ Fin k) (A : Fin k → Kernel K)
    (f : Signature K m) (g : Signature K n) :
    Signature.coordinateAction A (Tensor.reindex ports (Tensor.tensor f g)) =
      Tensor.reindex ports (Tensor.tensor
        (Signature.coordinateAction (fun j => A (ports (.inl j))) f)
        (Signature.coordinateAction (fun j => A (ports (.inr j))) g)) := by
  classical
  funext x
  simp only [Signature.coordinateAction, Tensor.reindex, Tensor.tensor]
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [← Fintype.sum_prod_type']
  apply Fintype.sum_equiv (splitWords ports)
  intro y
  have hp : (∏ i : Fin k, A i (x i) (y i)) =
      (∏ j : Fin m, A (ports (.inl j)) (x (ports (.inl j))) (y (ports (.inl j)))) *
      (∏ j : Fin n, A (ports (.inr j)) (x (ports (.inr j))) (y (ports (.inr j)))) := by
    rw [← ports.prod_comp (fun i => A i (x i) (y i)), Fintype.prod_sum_type]
  change (∏ i, A i (x i) (y i)) *
      (f (fun j => y (ports (.inl j))) * g (fun j => y (ports (.inr j)))) =
    ((∏ j, A (ports (.inl j)) (x (ports (.inl j))) (y (ports (.inl j)))) *
      f (fun j => y (ports (.inl j)))) *
    ((∏ j, A (ports (.inr j)) (x (ports (.inr j))) (y (ports (.inr j)))) *
      g (fun j => y (ports (.inr j))))
  rw [hp]
  ring

theorem action_scale {K : Type*} [CommSemiring K] {n : ℕ}
    (A : Fin n → Kernel K) (f : Signature K n) (c : K) :
    Signature.coordinateAction A (fun x => c * f x) =
      fun x => c * Signature.coordinateAction A f x := by
  funext x
  simp only [Signature.coordinateAction, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

/-- Local-affine disjoint closure twists each actual support block exactly
once. No false closure under adding phase-bearing dummy ports is assumed. -/
theorem localAffine_disjoint {m n k : ℕ} (ports : (Fin m ⊕ Fin n) ≃ Fin k)
    {f : Signature AlgebraicComplex m} {g : Signature AlgebraicComplex n}
    (hf : LocalAffine f) (hg : LocalAffine g) :
    LocalAffine (Tensor.reindex ports (Tensor.tensor f g)) := by
  intro alpha nonzero
  have hproduct : f (fun j => alpha (ports (.inl j))) *
      g (fun j => alpha (ports (.inr j))) ≠ 0 := nonzero
  have hf' := hf (fun j => alpha (ports (.inl j))) (mul_ne_zero_iff.mp hproduct).1
  have hg' := hg (fun j => alpha (ports (.inr j))) (mul_ne_zero_iff.mp hproduct).2
  unfold localTwist
  rw [action_disjoint]
  exact affine_disjoint ports hf' hg'

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G

/-- The literal original-field scalar and original ordered split survive the
fixed embedding and SAME inverse basis on every port. -/
theorem properSplit_action (B : InvertibleKernel) {f left right : AnySignature (OI.K G)}
    (split : ProperSplit f left right) :
    B.symm.action (embed G f).2 = fun x =>
      Holant.LocalDrafts.Hardness.OriginalFrozenForest.OriginalInput.embedding G (split.scale : OI.K G) *
        ((B.symm.action (embed G left).2) (fun j => x (split.ports (.inl j))) *
         (B.symm.action (embed G right).2) (fun j => x (split.ports (.inr j)))) := by
  let phi := (Holant.LocalDrafts.Hardness.OriginalFrozenForest.OriginalInput.embedding G).toRingHom
  change Signature.coordinateAction (fun _ => B.symm.matrix) (mapSignature phi f).2 = _
  rw [(split.map phi).equation, action_scale]
  change (fun x => phi (split.scale : OI.K G) *
    Signature.coordinateAction (fun _ => B.symm.matrix)
      (Tensor.reindex split.ports (Tensor.tensor (mapSignature phi left).2 (mapSignature phi right).2)) x) = _
  dsimp only [mapSignature]
  rw [action_disjoint]
  rfl

/-- No arbitrary proper-split closure callback is needed for the actual
three target classes. The common basis B remains the same for both factors. -/
theorem splitClosed_target (target : TargetClass) (B : InvertibleKernel) :
    SplitClosed G (leafPredicate G target.family B) := by
  intro f left right split hl hr
  cases target with
  | affine =>
      change Affine (B.symm.action (embed G left).2) at hl
      change Affine (B.symm.action (embed G right).2) at hr
      change Affine (B.symm.action (embed G f).2)
      rw [properSplit_action G B split]
      exact (affine_disjoint split.ports hl hr).scale _
  | product =>
      change Product (B.symm.action (embed G left).2) at hl
      change Product (B.symm.action (embed G right).2) at hr
      change Product (B.symm.action (embed G f).2)
      rw [properSplit_action G B split]
      exact (product_disjoint split.ports hl hr).scale _
  | localAffine =>
      change LocalAffine (B.symm.action (embed G left).2) at hl
      change LocalAffine (B.symm.action (embed G right).2) at hr
      change LocalAffine (B.symm.action (embed G f).2)
      rw [properSplit_action G B split]
      exact (localAffine_disjoint split.ports hl hr).scale _

/-- Relative original common presentation with proved class reconstruction.
Local membership and the mandatory transformed edge remain explicit. -/
theorem relative_original_common_presentation (P : Palette G) (target : TargetClass)
    (B : InvertibleKernel)
    (edge : (⟨2, kernelSignature (Kernel.pullback Signature.equality B.matrix)⟩ :
      AnySignature AlgebraicComplex) ∈ target.family)
    (leaves : LocalLeafTheorems G P (leafPredicate G target.family B)) :
    CommonTransformable target.family (originalFamily G) :=
  relative_common_presentation G P target.family B edge (splitClosed_target G target B) leaves

/-- Relative CURRENT common presentation, covering every old and new saved
prime, with the class split rule proved rather than supplied by the caller. -/
theorem relative_current_common_presentation (P : Palette G) (target : TargetClass)
    (B : InvertibleKernel)
    (edge : (⟨2, kernelSignature (Kernel.pullback Signature.equality B.matrix)⟩ :
      AnySignature AlgebraicComplex) ∈ target.family)
    (leaves : LocalCurrentTheorems G P (leafPredicate G target.family B)) :
    CommonTransformable target.family (currentFamily G P) :=
  CurrentFrontierClosure.relative_current_common_presentation G P target.family B edge
    (splitClosed_target G target B) leaves

theorem relative_current_tractx_criterion (P : Palette G) (target : TargetClass)
    (B : InvertibleKernel)
    (edge : (⟨2, kernelSignature (Kernel.pullback Signature.equality B.matrix)⟩ :
      AnySignature AlgebraicComplex) ∈ target.family)
    (leaves : LocalCurrentTheorems G P (leafPredicate G target.family B)) :
    TractX (currentFamily G P) :=
  CurrentFrontierClosure.relative_current_tractx_criterion G P target B edge
    (splitClosed_target G target B) leaves

end Holant.LocalDrafts.RemoteWork.StableClosureV2.FrontierSplitClosure
end
