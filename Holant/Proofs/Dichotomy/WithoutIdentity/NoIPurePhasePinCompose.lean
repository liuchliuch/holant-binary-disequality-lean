import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPurePhaseRecipeFactor
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPureUniformFour

/-! Flatten signed phase recipes through original pure-pin witnesses.
Every free coordinate occurs once, so incidence is preserved exactly;
pinned-coordinate phase constants remain as an explicit scalar. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePhasePinCompose
open Holant Holant.Tractable
open scoped BigOperators
namespace R
export NoIPurePhaseRecipeFactor (Port word incidence factor total)
end R
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
set_option maxRecDepth 16384
set_option Elab.async false
variable {n m r k : ℕ}

def PurePins (p : Fin n → Bool ⊕ Fin m) : Prop := ∀ j, ∃! i, p i = Sum.inr j

def substitute (p : Fin n → Bool ⊕ Fin m) (z : Fin m → Bool) : Fin n → Bool :=
  fun i => Sum.elim id z (p i)

def compose (p : Fin n → Bool ⊕ Fin m) (q : Fin m → R.Port r) : Fin n → R.Port r :=
  fun i => Sum.elim Sum.inl q (p i)

theorem word_compose (p : Fin n → Bool ⊕ Fin m) (q : Fin m → R.Port r)
    (z : Fin r → Bool) : R.word (compose p q) z = substitute p (R.word q z) := by
  funext i
  cases h : p i with
  | inl b => simp [R.word,compose,substitute,h]
  | inr j => simp [R.word,compose,substitute,h]

theorem sum_free {A : Type} [AddCommMonoid A] (p : Fin n → Bool ⊕ Fin m)
    (pure : PurePins p) (f : Fin m → A) :
    (∑ i : Fin n, Sum.elim (fun _ => 0) f (p i)) = ∑ j : Fin m, f j := by
  classical
  calc
    _ = ∑ i : Fin n, ∑ j : Fin m, if p i = Sum.inr j then f j else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      cases h : p i with
      | inl b => simp [h]
      | inr j => simp [h]
    _ = ∑ j : Fin m, ∑ i : Fin n, if p i = Sum.inr j then f j else 0 := Finset.sum_comm
    _ = ∑ j : Fin m, f j := by
      apply Finset.sum_congr rfl
      intro j _
      obtain ⟨i,hi,unique⟩ := pure j
      rw [Finset.sum_eq_single i]
      · simp [hi]
      · intro i' _ ne
        have h : p i' ≠ Sum.inr j := fun h => ne (unique i' h)
        simp [h]
      · simp

theorem incidence_compose (p : Fin n → Bool ⊕ Fin m) (pure : PurePins p)
    (q : Fin m → R.Port r) (j : Fin r) : R.incidence (compose p q) j = R.incidence q j := by
  unfold R.incidence
  have each (i : Fin n) :
      (match compose p q i with
      | .inl _ => (0:ℤ)
      | .inr (a,s) => if a=j then (if s then -1 else 1) else 0) =
      Sum.elim (fun _ => 0) (fun u => match q u with
        | .inl _ => (0:ℤ)
        | .inr (a,s) => if a=j then (if s then -1 else 1) else 0) (p i) := by
    cases h : p i <;> simp [compose,h]
  exact (Finset.sum_congr rfl (fun i _ => each i)).trans (sum_free p pure _)

def fixedWeight (p : Fin n → Bool ⊕ Fin m) : ℕ :=
  ∑ i, Sum.elim (fun b => if b then 1 else 0) (fun _ => 0) (p i)

theorem weight_substitute (p : Fin n → Bool ⊕ Fin m) (pure : PurePins p)
    (z : Fin m → Bool) : weight (substitute p z) = fixedWeight p + weight z := by
  unfold weight fixedWeight
  have each (i : Fin n) : (if substitute p z i then 1 else 0) =
      Sum.elim (fun b => if b then 1 else 0) (fun _ => 0) (p i) +
        Sum.elim (fun _ => 0) (fun j => if z j then 1 else 0) (p i) := by
    cases h : p i <;> simp [substitute,h]
  simp only [each,Finset.sum_add_distrib,sum_free p pure]

theorem uniform_four {K : Type} [Zero K] (f : Signature K n)
    (uniform : NoIPureChargeTwoFamily.UniformFour f)
    (p : Fin n → Bool ⊕ Fin m) (pure : PurePins p) :
    NoIPureChargeTwoFamily.UniformFour (fun z => f (substitute p z)) := by
  intro x y hx hy
  have same := uniform (substitute p x) (substitute p y) hx hy
  rw [weight_substitute p pure x,weight_substitute p pure y] at same
  omega

section Recipes
variable {ns ms : Fin k → ℕ}
variable (ps : (v : Fin k) → Fin (ns v) → Bool ⊕ Fin (ms v))
variable (pure : ∀ v, PurePins (ps v))
variable (qs : (v : Fin k) → Fin (ms v) → R.Port r)

include pure in
theorem total_compose : R.total (fun v => compose (ps v) (qs v)) = R.total qs := by
  funext j
  unfold R.total
  apply Finset.sum_congr rfl
  intro v _
  exact incidence_compose (ps v) (pure v) (qs v) j

include pure in
theorem factor_compose (a : AlgebraicComplex) :
    R.factor (fun v => compose (ps v) (qs v)) a =
      (∏ v, a ^ fixedWeight (ps v)) • R.factor qs a := by
  funext z
  simp only [R.factor,Pi.smul_apply,smul_eq_mul,word_compose,
    weight_substitute _ (pure _),pow_add,Finset.prod_mul_distrib]

theorem fixed_factor_nonzero (a : AlgebraicComplex) (nonzero : a ≠ 0) :
    (∏ v, a ^ fixedWeight (ps v)) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun _ _ => pow_ne_zero _ nonzero)

theorem recipe_compose {K : Type} [CommMonoid K]
    (f : (v : Fin k) → Signature K (ns v)) :
    (fun z => ∏ v, f v (R.word (compose (ps v) (qs v)) z)) =
      (fun z => ∏ v, (fun y => f v (substitute (ps v) y)) (R.word (qs v) z)) := by
  simp only [word_compose]
end Recipes


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePhasePinCompose
end
