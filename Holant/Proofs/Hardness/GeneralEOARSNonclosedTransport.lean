import Holant.Proofs.Hardness.GeneralEOARSNonclosedMass
import Holant.Proofs.Hardness.GeneralEOARSNonclosedSupport
import Holant.Proofs.Hardness.GeneralEOCentralHolePatterns

/-! Original-coordinate transport for the selected covariance obstruction.
All permutations retain every original port. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOARSNonclosedTransport
open Holant Holant.Tractable
namespace M
export GeneralEOARSNonclosedMass (mass correlation)
end M
namespace S
export GeneralEOARSNonclosedSupport (toggle FreePair)
end S
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

def words (e : Equiv.Perm (Fin n)) : (Fin n → Bool) ≃ (Fin n → Bool) where
  toFun x := x ∘ e
  invFun x := x ∘ e.symm
  left_inv := by intro x; funext i; simp
  right_inv := by intro x; funext i; simp

def reorder {K : Type*} (f : Signature K n) (e : Equiv.Perm (Fin n)) : Signature K n :=
  fun x => f (x ∘ e.symm)

theorem reordered_word {K : Type*} (f : Signature K n) (e : Equiv.Perm (Fin n))
    (x : Fin n → Bool) : reorder f e (x ∘ e) = f x := by
  unfold reorder
  congr 1
  funext i
  simp

theorem central {K : Type*} [CommSemiring K] (f : Signature K n)
    (he : Signature.CentralSupport f) (e : Equiv.Perm (Fin n)) :
    Signature.CentralSupport (reorder f e) := by
  intro x hx
  apply he
  have h : weight (x ∘ e.symm)=weight x :=
    Fintype.sum_equiv e.symm _ _ (fun _ => rfl)
  rwa [h]

theorem ars (f : Signature ℂ n) (hf : GeneralEOARSBoundary.ARSUpToScale f)
    (e : Equiv.Perm (Fin n)) : GeneralEOARSBoundary.ARSUpToScale (reorder f e) := by
  obtain ⟨c,hc,g,hg,rfl⟩ := hf
  refine ⟨c,hc,reorder g e,?_,rfl⟩
  intro x
  exact hg (x ∘ e.symm)

theorem correlation (f : Signature ℂ n) (e : Equiv.Perm (Fin n)) (i j : Fin n) :
    M.correlation (M.mass (reorder f e)) i j=M.correlation (M.mass f) (e i) (e j) := by
  unfold M.correlation
  apply Fintype.sum_equiv (words e.symm)
  intro x
  simp [M.mass,reorder,words,Function.comp_def]

theorem free_pair (f : Signature AlgebraicComplex n) (e : Equiv.Perm (Fin n))
    (i j : Fin n) (h : S.FreePair (reorder f e) i j) : S.FreePair f (e i) (e j) := by
  obtain ⟨hij,hop,hfree⟩ := h
  refine ⟨fun hh => hij (e.injective hh),?_,?_⟩
  · intro x hx
    exact hop (x ∘ e) (by rwa [reordered_word])
  · intro x hx
    have h := hfree (x ∘ e) (by rwa [reordered_word])
    have hw : S.toggle i j (x ∘ e) ∘ e.symm = S.toggle (e i) (e j) x := by
      funext k
      simp [S.toggle,Function.comp_def,Equiv.symm_apply_eq]
    change f (S.toggle i j (x ∘ e) ∘ e.symm)≠0 at h
    rwa [hw] at h

theorem prefix_permutation (i j : Fin (n+2)) (hij : i ≠ j) :
    ∃e : Equiv.Perm (Fin (n+2)), e 0=i ∧ e 1=j := by
  have hi : Function.Injective (![i,j] : Fin 2 → Fin (n+2)) := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all
  obtain ⟨h,e,he⟩ := GeneralEOCentralHolePatterns.exists_prefix_permutation ![i,j] hi
  refine ⟨e,?_,?_⟩
  · simpa using he 0
  · have h1 : Fin.castLE h (1 : Fin 2)=(1 : Fin (n+2)) := by
      apply Fin.ext
      simp [Nat.mod_eq_of_lt (show 1<n+2 by omega)]
    simpa [h1] using he 1

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOARSNonclosedTransport
