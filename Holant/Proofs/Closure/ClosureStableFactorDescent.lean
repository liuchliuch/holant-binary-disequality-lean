import Holant.Proofs.Closure.ClosureTensorPrimeFactors
import Holant.Proofs.FiniteGroups.Stabilization.FactorBaseChange

/-! Exact descent when the fixed left factor is already an original-field
table. The same ordered partition and the literal left table are retained;
only the residual factor is recovered by a nonzero original-field pivot. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureStableFactor
open Holant Holant.LocalDrafts.FinitePGL2.Stabilization
variable {L E : Type*} [Field L] [Field E] {n k q : ℕ}

theorem known_left_descends (φ : L →+* E) (f : Signature L n) (B : Signature L k)
    (nonzero : B≠0) (R : Signature E q)
    (s : ProperSplit (mapSignature φ (⟨n,f⟩ : AnySignature L))
      (mapSignature φ (⟨k,B⟩ : AnySignature L)) ⟨q,R⟩) :
    ∃ right : Signature L q, ∃ split : ProperSplit (⟨n,f⟩ : AnySignature L) ⟨k,B⟩ ⟨q,right⟩,
      split.ports=s.ports ∧ split.scale=1 := by
  classical
  dsimp only [mapSignature] at s ⊢
  obtain ⟨pivot,live⟩ : ∃ x,B x≠0 := by
    by_contra none
    push Not at none
    exact nonzero (funext none)
  let join : (Fin k → Bool) → (Fin q → Bool) → (Fin n → Bool) :=
    fun x y i => Sum.elim x y (s.ports.symm i)
  have join_left (x : Fin k → Bool) (y : Fin q → Bool) (i : Fin k) :
      join x y (s.ports (.inl i))=x i := by
    simp only [join,Equiv.symm_apply_apply]
    rfl
  have join_right (x : Fin k → Bool) (y : Fin q → Bool) (i : Fin q) :
      join x y (s.ports (.inr i))=y i := by
    simp only [join,Equiv.symm_apply_apply]
    rfl
  have equation (x : Fin k → Bool) (y : Fin q → Bool) :
      φ (f (join x y))=(s.scale : E)*(φ (B x)*R y) := by
    have h := congrFun s.equation (join x y)
    have left : (fun i => join x y (s.ports (.inl i)))=x := funext (join_left x y)
    have right : (fun i => join x y (s.ports (.inr i)))=y := funext (join_right x y)
    change φ (f (join x y))=(s.scale : E)*
      (φ (B (fun i => join x y (s.ports (.inl i)))) * R (fun i => join x y (s.ports (.inr i)))) at h
    rw [left,right] at h
    exact h
  let right : Signature L q := fun y => f (join pivot y)/B pivot
  have exactFactor (x : Fin k → Bool) (y : Fin q → Bool) : f (join x y)=B x*right y := by
    have cross : φ (f (join x y)*B pivot)=φ (B x*f (join pivot y)) := by
      rw [map_mul,map_mul,equation x y,equation pivot y]
      ring
    have h := φ.injective cross
    dsimp only [right]
    field_simp [live]
    exact h
  refine ⟨right,{
    left_pos := s.left_pos
    right_pos := s.right_pos
    ports := s.ports
    scale := 1
    equation := ?_ },rfl,rfl⟩
  funext w
  have reconstruct : join (fun i => w (s.ports (.inl i))) (fun i => w (s.ports (.inr i)))=w := by
    funext i
    obtain ⟨j,rfl⟩ := s.ports.surjective i
    cases j <;> simp only [join,Equiv.symm_apply_apply] <;> rfl
  have h := exactFactor (fun i => w (s.ports (.inl i))) (fun i => w (s.ports (.inr i)))
  rw [reconstruct] at h
  simpa only [Units.val_one,one_mul] using h

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureStableFactor
