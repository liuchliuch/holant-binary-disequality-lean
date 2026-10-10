import Holant.Proofs.Closure.HistorySectorNormalizedEndpoint

/-! Per-port invertible tensor action over the SAME source field. Each split's
actual original port partition and nonzero source unit remain unchanged; the
matrices on its two factors are the restrictions through that exact partition.
No matrix is declared a gadget or a new field. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.HistorySectorNormalizedPortAction
open Holant Holant.Tractable Holant.Marked
open Holant.LocalDrafts.FinitePGL2.Stabilization
open HistorySectorCardsAlgebra
variable {L : Type*} [Field L]

def signature (f : AnySignature L) (A : Fin f.1 → Kernel L) : AnySignature L :=
  ⟨f.1,Signature.coordinateAction A f.2⟩

def split {f a b : AnySignature L} (A : Fin f.1 → Kernel L) (S : ProperSplit f a b) :
    ProperSplit (signature f A)
      (signature a (fun i => A (S.ports (.inl i))))
      (signature b (fun i => A (S.ports (.inr i)))) where
  left_pos := S.left_pos
  right_pos := S.right_pos
  ports := S.ports
  scale := S.scale
  equation := by
    change Signature.coordinateAction A f.2 = _
    rw [S.equation,ClosureFactorTreeAction.coordinateAction_scale]
    change (fun x => (S.scale : L) * Signature.coordinateAction A
      (Tensor.reindex S.ports (Tensor.tensor a.2 b.2)) x) = _
    rw [ClosureFactorTreeAction.coordinateAction_tensor]
    rfl

@[simp] theorem split_ports {f a b : AnySignature L} (A : Fin f.1 → Kernel L) (S : ProperSplit f a b) :
    (split A S).ports = S.ports := rfl
@[simp] theorem split_scale {f a b : AnySignature L} (A : Fin f.1 → Kernel L) (S : ProperSplit f a b) :
    (split A S).scale = S.scale := rfl

theorem signature_inverse (f : AnySignature L) (A B : Fin f.1 → Kernel L)
    (inverse : ∀ i, Kernel.mul (B i) (A i) = Signature.equality) :
    signature (signature f A) B = f := by
  cases f
  unfold signature
  rw [Signature.coordinateAction_cancel B A inverse]

/-- A LEFT inverse at every recorded original port already preserves Prime. -/
theorem prime (f : AnySignature L) (A B : Fin f.1 → Kernel L)
    (inverse : ∀ i, Kernel.mul (B i) (A i) = Signature.equality) (hf : Prime f) :
    Prime (signature f A) := by
  refine ⟨?_,?_⟩
  · intro hz
    have h := congrArg (Signature.coordinateAction B) hz
    change Signature.coordinateAction B (Signature.coordinateAction A f.2) =
      Signature.coordinateAction B (0 : Signature L f.1) at h
    rw [Signature.coordinateAction_cancel B A inverse,Signature.coordinateAction_zero] at h
    exact hf.1 h
  · rintro ⟨a,b,⟨S⟩⟩
    have h : Nonempty (ProperSplit f
        (signature a (fun i => B (S.ports (.inl i))))
        (signature b (fun i => B (S.ports (.inr i))))) := by
      simpa only [signature_inverse f A B inverse] using
        (⟨split (f:=signature f A) B S⟩ : Nonempty (ProperSplit (signature (signature f A) B)
          (signature a (fun i => B (S.ports (.inl i))))
          (signature b (fun i => B (S.ports (.inr i))))))
    exact hf.2 ⟨_,_,h⟩

theorem prime_iff (f : AnySignature L) (A B : Fin f.1 → Kernel L)
    (leftInverse : ∀ i, Kernel.mul (B i) (A i) = Signature.equality)
    (rightInverse : ∀ i, Kernel.mul (A i) (B i) = Signature.equality) :
    Prime (signature f A) ↔ Prime f := by
  constructor
  · intro h
    simpa only [signature_inverse f A B leftInverse] using
      prime (signature f A) B A rightInverse h
  · exact prime f A B leftInverse

theorem fold_action {n : ℕ} (C : Fin n → Kernel L) (is : List (Fin n))
    (distinct : is.Nodup) (f : Signature L n) :
    is.foldl (fun g i => Signature.coordinateAction (atPort i (C i)) g) f =
      Signature.coordinateAction (fun i => if i ∈ is then C i else Signature.equality) f := by
  classical
  induction is generalizing f with
  | nil => simp [Signature.coordinateAction_equality]
  | cons i is ih =>
    rw [List.foldl_cons,ih distinct.tail,Signature.coordinateAction_comp]
    congr 1
    funext j
    by_cases hj : j = i
    · subst j
      have hi : i ∉ is := (List.nodup_cons.mp distinct).1
      simp [atPort,hi]
    · simp [atPort,hj]

theorem full_fold_action {n : ℕ} (C : Fin n → Kernel L) (f : Signature L n) :
    (List.finRange n).foldl (fun g i => Signature.coordinateAction (atPort i (C i)) g) f =
      Signature.coordinateAction C f := by
  simpa using fold_action C (List.finRange n) (List.nodup_finRange n) f

end Holant.LocalDrafts.RemoteWork.StableClosureV2.HistorySectorNormalizedPortAction
end
