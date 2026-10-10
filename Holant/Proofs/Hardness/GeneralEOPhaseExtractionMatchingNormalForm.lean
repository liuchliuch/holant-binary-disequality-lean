import Holant.Proofs.Hardness.GeneralEOPhaseExtractionClosedTomography

/-! Every complete native closure can be represented by one original boundary
permutation followed by adjacent pair contractions. Conversely, that normal
form is an actual native closure of the original network. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseExtractionMatchingNormalForm
open Holant
namespace H
export GeneralEOPhaseExtractionLoopTomography (merge merge_denote)
end H
namespace O
export GeneralEOPinnedDescentOperations (word)
end O
namespace N
export GeneralEOPhaseExtractionClosedTomography (NativeClosure)
end N
namespace R
export GeneralEOPinnedDescentNetwork (reboundary reboundary_denote)
end R
namespace D
export GeneralEOPhaseExtractionDistance (loop)
end D
set_option backward.isDefEq.respectTransparency false

/-- Extend a permutation by fixing the new first coordinate. -/
def liftPerm {n : ℕ} (p : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n+1)) where
  toFun := Fin.cases 0 (fun i => (p i).succ)
  invFun := Fin.cases 0 (fun i => (p.symm i).succ)
  left_inv i := by
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · simp
  right_inv i := by
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · simp

@[simp] theorem liftPerm_zero {n : ℕ} (p : Equiv.Perm (Fin n)) : liftPerm p 0=0 := rfl
@[simp] theorem liftPerm_succ {n : ℕ} (p : Equiv.Perm (Fin n)) (i : Fin n) :
    liftPerm p i.succ=(p i).succ := rfl

def tailPerm {n : ℕ} (p : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n+2)) :=
  liftPerm (liftPerm p)

theorem word_tailPerm {n : ℕ} (p : Equiv.Perm (Fin n)) (u v : Bool) (x : Fin n→Bool) :
    O.word u v x ∘ tailPerm p=O.word u v (x ∘ p) := by
  funext i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i <;> rfl

/-- Moving a tail permutation before a native loop acts on the original
ports by the explicitly extended permutation. -/
theorem merge_tail {n : ℕ} (f : Signature ℂ (n+2))
    (e : Equiv.Perm (Fin (n+2))) (p : Equiv.Perm (Fin n)) :
    Tensor.reindex p (H.merge f e)=H.merge f (e.trans (tailPerm p)) := by
  funext x
  change f (O.word false true (x ∘ p) ∘ e)+f (O.word true false (x ∘ p) ∘ e)=_
  rw [←word_tailPerm p false true x,←word_tailPerm p true false x]
  rfl

def value : (k : ℕ) → Signature ℂ (2*k) → ℂ
  | 0,f => f Fin.elim0
  | k+1,f => value k (H.merge f (Equiv.refl _))

theorem value_step (k : ℕ) (f : Signature ℂ (2*(k+1)))
    (e : Equiv.Perm (Fin (2*(k+1)))) (p : Equiv.Perm (Fin (2*k))) :
    value k (Tensor.reindex p (H.merge f e))=
      value (k+1) (Tensor.reindex (e.trans (tailPerm p)) f) := by
  rw [merge_tail]
  rfl

/-- Canonical contraction is implemented on the actual input graph. -/
def close : (k : ℕ) → Network ℂ (2*k) → Network ℂ 0
  | 0,S => S
  | k+1,S => close k (D.loop (R.reboundary S (Equiv.refl _)))

theorem close_trace (k : ℕ) (S : Network ℂ (2*k)) : N.NativeClosure S (close k S) := by
  induction k with
  | zero => exact .done S
  | succ k ih => exact .step S (Equiv.refl _) (ih _)

theorem close_value (k : ℕ) (S : Network ℂ (2*k)) :
    (close k S).denote Fin.elim0=value k S.denote := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [close,ih,H.merge_denote]
    rfl

/-- All coordinate choices made during a complete native closure combine to
one permutation of the original boundary. No matching is postulated. -/
theorem normal_form (k : ℕ) (S : Network ℂ (2*k)) {Q : Network ℂ 0}
    (h : N.NativeClosure S Q) :
    ∃e : Equiv.Perm (Fin (2*k)),Q.denote Fin.elim0=value k (Tensor.reindex e S.denote) := by
  induction k with
  | zero =>
    cases h with
    | done S => exact ⟨Equiv.refl _,rfl⟩
  | succ k ih =>
    cases h with
    | step S e tail =>
      obtain ⟨p,hp⟩ := ih _ tail
      refine ⟨e.trans (tailPerm p),?_⟩
      rw [H.merge_denote] at hp
      exact hp.trans (value_step k S.denote e p)

/-- Every permutation normal form is attained by an actual native closure. -/
theorem realize (k : ℕ) (S : Network ℂ (2*k)) (e : Equiv.Perm (Fin (2*k))) :
    ∃Q : Network ℂ 0,
      N.NativeClosure S Q ∧ Q.denote Fin.elim0=value k (Tensor.reindex e S.denote) := by
  cases k with
  | zero =>
    refine ⟨S,.done S,?_⟩
    change S.denote Fin.elim0=S.denote (Fin.elim0 ∘ e)
    congr 1
  | succ k =>
    let U := D.loop (R.reboundary S e)
    refine ⟨close k U,.step S e (close_trace k U),?_⟩
    rw [close_value,H.merge_denote]
    rfl

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseExtractionMatchingNormalForm
