import Holant.Tractable.CommonTransform
import Holant.Proofs.Reductions.FactorSaturation.Reconstruction

/-! All-arity algebraic coordinate transport of the SAME saved factor tree.
Every split unit and ordered port partition is retained. Slots and prime-leaf
addresses are transported bijectively, including repeated equal resources.
This is an analytic transport theorem, not a claim that the basis is a gadget
or that its entries lie in the original source coefficient field. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureFactorTreeAction
open Holant Holant.Tractable Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.Hardness
open scoped BigOperators

private def splitWords {m n k : ℕ} (ports : (Fin m ⊕ Fin n) ≃ Fin k) :
    (Fin k → Bool) ≃ ((Fin m → Bool) × (Fin n → Bool)) :=
  (Equiv.arrowCongr ports.symm (Equiv.refl Bool)).trans
    (Equiv.sumArrowEquivProdArrow (Fin m) (Fin n) Bool)

theorem coordinateAction_tensor {K : Type*} [CommSemiring K] {m n k : ℕ}
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

theorem coordinateAction_scale {K : Type*} [CommSemiring K] {n : ℕ}
    (A : Fin n → Kernel K) (f : Signature K n) (c : K) :
    Signature.coordinateAction A (fun x => c * f x) =
      fun x => c * Signature.coordinateAction A f x := by
  funext x
  simp only [Signature.coordinateAction, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

@[simp] theorem action_zero (B : InvertibleKernel) (n : ℕ) :
    B.action (0 : Signature AlgebraicComplex n) = 0 := by
  funext x
  simp [InvertibleKernel.action,Signature.coordinateAction]

def signature (B : InvertibleKernel) (f : AnySignature AlgebraicComplex) :
    AnySignature AlgebraicComplex := ⟨f.1,B.action f.2⟩

@[simp] theorem signature_inverse (B : InvertibleKernel) (f : AnySignature AlgebraicComplex) :
    signature B.symm (signature B f) = f := by
  cases f
  simp [signature]

def split (B : InvertibleKernel) {f a b : AnySignature AlgebraicComplex}
    (s : ProperSplit f a b) : ProperSplit (signature B f) (signature B a) (signature B b) where
  left_pos := s.left_pos
  right_pos := s.right_pos
  ports := s.ports
  scale := s.scale
  equation := by
    change Signature.coordinateAction (fun _ => B.matrix) f.2 = _
    rw [s.equation,coordinateAction_scale]
    change (fun x => (s.scale : AlgebraicComplex) *
      Signature.coordinateAction (fun _ => B.matrix)
        (Tensor.reindex s.ports (Tensor.tensor a.2 b.2)) x) = _
    rw [coordinateAction_tensor]
    rfl

@[simp] theorem split_ports (B : InvertibleKernel) {f a b : AnySignature AlgebraicComplex}
    (s : ProperSplit f a b) : (split B s).ports = s.ports := rfl
@[simp] theorem split_scale (B : InvertibleKernel) {f a b : AnySignature AlgebraicComplex}
    (s : ProperSplit f a b) : (split B s).scale = s.scale := rfl

theorem prime (B : InvertibleKernel) (f : AnySignature AlgebraicComplex) (hf : Prime f) :
    Prime (signature B f) := by
  refine ⟨?_,?_⟩
  · intro zero
    have inverse := B.symm_action_action f.2
    change B.action f.2 = 0 at zero
    rw [zero,action_zero] at inverse
    exact hf.1 inverse.symm
  · rintro ⟨a,b,⟨s⟩⟩
    have inverse : Nonempty (ProperSplit f (signature B.symm a) (signature B.symm b)) := by
      simpa only [signature_inverse] using (⟨split B.symm s⟩ :
        Nonempty (ProperSplit (signature B.symm (signature B f))
          (signature B.symm a) (signature B.symm b)))
    exact hf.2 ⟨signature B.symm a,signature B.symm b,inverse⟩

theorem prime_iff (B : InvertibleKernel) (f : AnySignature AlgebraicComplex) :
    Prime (signature B f) ↔ Prime f := by
  constructor
  · intro hf
    simpa only [signature_inverse] using prime B.symm (signature B f) hf
  · exact prime B f

def tree (B : InvertibleKernel) {f : AnySignature AlgebraicComplex} :
    FactorTree f → FactorTree (signature B f)
  | .leaf f hf => .leaf (signature B f) (prime B f hf)
  | .split s l r => .split (split B s) (tree B l) (tree B r)

def occurrence (B : InvertibleKernel) (o : TreeOccurrence AlgebraicComplex) :
    TreeOccurrence AlgebraicComplex := ⟨signature B o.1,tree B o.2⟩

theorem leaves (B : InvertibleKernel) {f : AnySignature AlgebraicComplex} (t : FactorTree f) :
    (tree B t).leaves = t.leaves.map (signature B) := by
  induction t with
  | leaf => simp [tree,FactorTree.leaves]
  | split s l r ihl ihr => simp [tree,FactorTree.leaves,ihl,ihr]

def slots (B : InvertibleKernel) {f : AnySignature AlgebraicComplex} (t : FactorTree f) :
    FactorSaturation.Slots t ≃ FactorSaturation.Slots (tree B t) := match t with
  | .leaf _ _ => Equiv.refl Unit
  | .split _ l r => Equiv.sumCongr (Equiv.refl Unit) (Equiv.sumCongr (slots B l) (slots B r))

theorem slot_exact (B : InvertibleKernel) {f : AnySignature AlgebraicComplex}
    (t : FactorTree f) (i : FactorSaturation.Slots t) :
    FactorSaturation.slot (tree B t) (slots B t i) = occurrence B (FactorSaturation.slot t i) := by
  induction t with
  | leaf => rfl
  | split s l r ihl ihr =>
      rcases i with u | (i | i)
      · rfl
      · exact ihl i
      · exact ihr i

theorem path_exact (B : InvertibleKernel) {f : AnySignature AlgebraicComplex}
    (t : FactorTree f) (i : FactorSaturation.Slots t) :
    FactorSaturation.path (tree B t) (slots B t i) = FactorSaturation.path t i := by
  induction t with
  | leaf => rfl
  | split s l r ihl ihr =>
      rcases i with u | (i | i)
      · rfl
      · exact congrArg (List.cons false) (ihl i)
      · exact congrArg (List.cons true) (ihr i)

def leafSlots (B : InvertibleKernel) {f : AnySignature AlgebraicComplex} (t : FactorTree f) :
    FactorSaturation.Leaves t ≃ FactorSaturation.Leaves (tree B t) := match t with
  | .leaf _ _ => Equiv.refl Unit
  | .split _ l r => Equiv.sumCongr (leafSlots B l) (leafSlots B r)

theorem leafSlot_exact (B : InvertibleKernel) {f : AnySignature AlgebraicComplex}
    (t : FactorTree f) (i : FactorSaturation.Leaves t) :
    FactorSaturation.leafSlot (tree B t) (leafSlots B t i) =
      slots B t (FactorSaturation.leafSlot t i) := by
  induction t with
  | leaf => rfl
  | split s l r ihl ihr =>
      cases i with
      | inl i => exact congrArg (fun x => Sum.inr (Sum.inl x)) (ihl i)
      | inr i => exact congrArg (fun x => Sum.inr (Sum.inr x)) (ihr i)

theorem leaf_exact (B : InvertibleKernel) {f : AnySignature AlgebraicComplex}
    (t : FactorTree f) (i : FactorSaturation.Leaves t) :
    FactorSaturation.leaf (tree B t) (leafSlots B t i) = signature B (FactorSaturation.leaf t i) := by
  unfold FactorSaturation.leaf
  rw [leafSlot_exact,slot_exact]
  rfl

theorem leaf_card (B : InvertibleKernel) {f : AnySignature AlgebraicComplex} (t : FactorTree f) :
    Fintype.card (FactorSaturation.Leaves (tree B t)) = Fintype.card (FactorSaturation.Leaves t) :=
  (Fintype.card_congr (leafSlots B t)).symm

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureFactorTreeAction
end
