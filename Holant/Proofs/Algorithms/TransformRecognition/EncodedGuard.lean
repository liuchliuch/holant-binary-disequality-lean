import Holant.Proofs.BinaryInterpolation.EffectiveRecognition.NullstellensatzSearch.Arithmetic


namespace Holant.LocalDrafts.MainChain.TransformRecognition.EncodedGuard
open MvPolynomial Holant.LocalDrafts.EffectiveAlgebraic
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.NullstellensatzSearch
variable {m k n : ℕ}

def hit (j : Fin n) : Fin n → ℕ := fun i => if i=j then 1 else 0

def equation (oneSlot negSlot : Fin m) : EncodedSystem.Equation m (5+k) :=
  [(oneSlot, hit (Fin.castAdd k 4) + hit (Fin.castAdd k 0) + hit (Fin.castAdd k 3)),
   (negSlot, hit (Fin.castAdd k 4) + hit (Fin.castAdd k 1) + hit (Fin.castAdd k 2)),
   (negSlot,0)]

def augment (oneSlot negSlot : Fin m) (S : EncodedSystem.System m (5+k)) :
    EncodedSystem.System m (5+k) := equation oneSlot negSlot :: S

noncomputable section
variable {R : Type*} [CommRing R]

@[simp] theorem hit_eval (y : Fin n → R) (j : Fin n) :
    (∏ i, y i ^ hit j i) = y j := by
  simp [hit]

theorem plus_eval (y : Fin n → R) (a b : Fin n → ℕ) :
    (∏ i, y i ^ (a+b) i) = (∏ i, y i ^ a i) * (∏ i, y i ^ b i) := by
  simp only [Pi.add_apply,pow_add,Finset.prod_mul_distrib]

theorem equation_eval (w : Fin m → R) (oneSlot negSlot : Fin m)
    (h₁ : w oneSlot = 1) (hneg : w negSlot = -1) (y : Fin (5+k) → R) :
    eval₂ (RingHom.id R) y
      (NullstellensatzSearch.equation w (equation oneSlot negSlot)) =
    y (Fin.castAdd k 4) * (y (Fin.castAdd k 0)*y (Fin.castAdd k 3) -
      y (Fin.castAdd k 1)*y (Fin.castAdd k 2)) - 1 := by
  simp [equation,NullstellensatzSearch.equation,pow_add,
    Finset.prod_mul_distrib,hit_eval,h₁,hneg]
  ring

/-- Presence of the literal emitted row derives the guard from ordinary
system satisfaction, so positive completeness has no extra matrix premise. -/
theorem of_system (w : Fin m → R) (oneSlot negSlot : Fin m)
    (h₁ : w oneSlot = 1) (hneg : w negSlot = -1)
    (S : EncodedSystem.System m (5+k)) (y : Fin (5+k) → R)
    (hy : ∀ e ∈ augment oneSlot negSlot S,
      eval₂ (RingHom.id R) y (NullstellensatzSearch.equation w e)=0) :
    y (Fin.castAdd k 4) * (y (Fin.castAdd k 0)*y (Fin.castAdd k 3) -
      y (Fin.castAdd k 1)*y (Fin.castAdd k 2)) = 1 := by
  have h := hy (equation oneSlot negSlot) (List.mem_cons_self ..)
  rw [equation_eval w oneSlot negSlot h₁ hneg] at h
  exact sub_eq_zero.mp h

end
end Holant.LocalDrafts.MainChain.TransformRecognition.EncodedGuard
