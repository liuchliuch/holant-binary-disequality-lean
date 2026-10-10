import Holant.Proofs.Closure.ClosureRootPencilProduct

/-! A rooted matching product supported on every word of an anchor product
has vanishing Segre update minors in the anchor's exact ordered coordinates.
The edge alignment is derived from support, without an assumed common
matching, ruling, or tensor factorization in those coordinates. -/
noncomputable section
set_option maxRecDepth 10000
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureRootPencil
open Holant Holant.Projective
open scoped BigOperators

namespace Product
variable {m : ℕ} {f g : Signature ℂ 4}

theorem word_update_of_index (P : Product m f) (a b : Fin 2 → Bool)
    (k : Fin 2) (i : Fin 4) (hi : (P.ports.symm i).1 = k) :
    P.word (Function.update a k (b k)) i = P.word b i := by
  classical
  simp [word, hi]

theorem word_update_of_ne (P : Product m f) (a : Fin 2 → Bool)
    (k : Fin 2) (v : Bool) (i : Fin 4) (hi : (P.ports.symm i).1 ≠ k) :
    P.word (Function.update a k v) i = P.word a i := by
  classical
  simp only [word, Function.update_of_ne hi]

theorem word_update_flip (P : Product m f) (a : Fin 2 → Bool) (i : Fin 4) :
    P.word (Function.update a (P.ports.symm i).1 (!(a (P.ports.symm i).1))) i =
      !(P.word a i) := by
  classical
  cases hs : (P.ports.symm i).2 <;>
    cases ha : a (P.ports.symm i).1 <;>
    cases hp : P.parity (P.ports.symm i).1 <;>
    simp [word, hs, ha, hp]

private theorem flipped_parity_impossible (a b p : Bool)
    (h : b = (a ^^ p)) (hflip : b = ((!a) ^^ p)) : False := by
  revert a b p
  decide

/-- Every actual edge lies within one anchor edge. This follows from all
anchor words being supported, by changing just one anchor coordinate. -/
theorem anchor_index_eq (P : Product m f) (E : Product m g)
    (hs : ∀ a : Fin 2 → Bool, g (P.word a) ≠ 0) (e : Fin 2) :
    (P.ports.symm (E.ports (e,false))).1 =
      (P.ports.symm (E.ports (e,true))).1 := by
  classical
  let u := E.ports (e,false)
  let v := E.ports (e,true)
  change (P.ports.symm u).1 = (P.ports.symm v).1
  by_contra h
  let a : Fin 2 → Bool := fun _ => false
  let b := Function.update a (P.ports.symm u).1 (!(a (P.ports.symm u).1))
  have hflip : P.word b u = !(P.word a u) := P.word_update_flip a u
  have hstay : P.word b v = P.word a v :=
    P.word_update_of_ne a _ _ v (Ne.symm h)
  have ha := (E.parity_spec e _ _).mp ((E.supported (P.word a)).mp (hs a) e)
  have hb := (E.parity_spec e _ _).mp ((E.supported (P.word b)).mp (hs b) e)
  change P.word a v = (P.word a u ^^ E.parity e) at ha
  change P.word b v = (P.word b u ^^ E.parity e) at hb
  rw [hflip, hstay] at hb
  exact flipped_parity_impossible _ _ _ ha hb

/-- One actual factor evaluated in the anchor's original coordinates. -/
def anchoredFactor (P : Product m f) (E : Product m g)
    (e : Fin 2) (a : Fin 2 → Bool) : ℂ :=
  E.matrix e (P.word a (E.ports (e,false))) (P.word a (E.ports (e,true)))

theorem anchored_equation (P : Product m f) (E : Product m g) (a : Fin 2 → Bool) :
    g (P.word a) = E.scalar * ∏ e, P.anchoredFactor E e a := by
  simpa only [anchoredFactor] using congrFun E.equation (P.word a)

theorem anchoredFactor_update_minor (P : Product m f) (E : Product m g)
    (hs : ∀ a : Fin 2 → Bool, g (P.word a) ≠ 0)
    (e : Fin 2) (a b : Fin 2 → Bool) (k : Fin 2) :
    P.anchoredFactor E e a * P.anchoredFactor E e b =
      P.anchoredFactor E e (Function.update a k (b k)) *
        P.anchoredFactor E e (Function.update b k (a k)) := by
  classical
  have he := P.anchor_index_eq E hs e
  unfold anchoredFactor
  by_cases h : (P.ports.symm (E.ports (e,false))).1 = k
  · have h' : (P.ports.symm (E.ports (e,true))).1 = k := he.symm.trans h
    rw [P.word_update_of_index a b k _ h, P.word_update_of_index a b k _ h',
      P.word_update_of_index b a k _ h, P.word_update_of_index b a k _ h']
    exact mul_comm _ _
  · have h' : (P.ports.symm (E.ports (e,true))).1 ≠ k := by
      rw [← he]
      exact h
    rw [P.word_update_of_ne a k (b k) _ h, P.word_update_of_ne a k (b k) _ h',
      P.word_update_of_ne b k (a k) _ h, P.word_update_of_ne b k (a k) _ h']

/-- All Segre update minors vanish in the anchor's exact two-edge
coordinates. The matching alignment is a conclusion of the support premise. -/
theorem update_minor (P : Product m f) (E : Product m g)
    (hs : ∀ a : Fin 2 → Bool, g (P.word a) ≠ 0)
    (a b : Fin 2 → Bool) (k : Fin 2) :
    g (P.word a) * g (P.word b) =
      g (P.word (Function.update a k (b k))) *
        g (P.word (Function.update b k (a k))) := by
  classical
  calc
    g (P.word a) * g (P.word b) =
        (E.scalar * E.scalar) *
          ∏ e, (P.anchoredFactor E e a * P.anchoredFactor E e b) := by
      rw [P.anchored_equation E a, P.anchored_equation E b, Finset.prod_mul_distrib]
      ring
    _ = (E.scalar * E.scalar) *
        ∏ e, (P.anchoredFactor E e (Function.update a k (b k)) *
          P.anchoredFactor E e (Function.update b k (a k))) := by
      congr 1
      apply Finset.prod_congr rfl
      intro e _
      exact P.anchoredFactor_update_minor E hs e a b k
    _ = g (P.word (Function.update a k (b k))) *
        g (P.word (Function.update b k (a k))) := by
      rw [P.anchored_equation E (Function.update a k (b k)),
        P.anchored_equation E (Function.update b k (a k)), Finset.prod_mul_distrib]
      ring

/-- The same minor consequence with the literal support inclusion premise. -/
theorem update_minor_of_support_subset (P : Product m f) (E : Product m g)
    (hs : support f ⊆ support g) (a b : Fin 2 → Bool) (k : Fin 2) :
    g (P.word a) * g (P.word b) =
      g (P.word (Function.update a k (b k))) *
        g (P.word (Function.update b k (a k))) := by
  apply P.update_minor E _ a b k
  intro c
  exact (mem_support g _).mp (hs ((mem_support f _).mpr (P.word_supported c)))

end Product
end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureRootPencil
