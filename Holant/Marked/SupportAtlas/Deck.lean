import Holant.Marked.SupportAtlas.Coset

/-! The actual two-term weighted cards, at all ordered deleted and residual ports.
Every unordered pair and both orientations occur among the 24 permutations. -/
noncomputable section
namespace Holant.Marked.SupportAtlas
open Holant.Projective

def join (e : Equiv.Perm (Fin 4)) (a b u v : Bool) : Word :=
  fun i => (![a,b,u,v] : Word) (e.symm i)

@[simp] theorem fill_eq_join (e : Equiv.Perm (Fin 4)) (a p u v : Bool) :
    fill e a p u v = join e a (a ^^ p) u v := rfl

def slice (q : Signature ℂ 4) (e : Equiv.Perm (Fin 4)) (a p : Bool) : CMat :=
  fun u v => q (fill e a p u v)

def effectiveKernel (d : ℂ) (p : Bool) (t : ℂ) : CMat :=
  if p then (fun a b => if a then (if b then 0 else d) else (if b then t else 0))
  else diagonalC (d*t)

/-- Literal contraction sum with the source's diagonal or off-diagonal effective kernel. -/
def weightedCard (d : ℂ) (q : Signature ℂ 4) (e : Equiv.Perm (Fin 4))
    (p : Bool) (t : ℂ) : CMat :=
  fun u v => ∑ a : Bool, ∑ b : Bool, effectiveKernel d p t a b * q (join e a b u v)

theorem weightedCard_even (d : ℂ) (q : Signature ℂ 4) (e : Equiv.Perm (Fin 4)) (t : ℂ) :
    weightedCard d q e false t = binaryPencil (slice q e false false) (d • slice q e true false) t := by
  funext u v
  simp [weightedCard, effectiveKernel, diagonalC, binaryPencil, slice, fill_eq_join]
  ring

theorem weightedCard_odd (d : ℂ) (q : Signature ℂ 4) (e : Equiv.Perm (Fin 4)) (t : ℂ) :
    weightedCard d q e true t = binaryPencil (d • slice q e true true) (slice q e false true) t := by
  funext u v
  simp [weightedCard, effectiveKernel, binaryPencil, slice, fill_eq_join, add_comm]

/-- All actual oriented weighted contractions, with zero samples allowed. -/
def SafeDeck (m : ℕ) (d : ℂ) (q : Signature ℂ 4) : Prop :=
  ∀ (e : Equiv.Perm (Fin 4)) (p : Bool) (t : ℂ), t^m=1 → SafeWeighted m d (weightedCard d q e p t)

theorem deck_endpoint_pattern {m : ℕ} (hm : 3 ≤ m) (d : ℂ) (hd : d ≠ 0)
    (hdroot : (d^2)^m=1) (q : Signature ℂ 4) (h : SafeDeck m d q)
    (e : Equiv.Perm (Fin 4)) (p : Bool) : MatrixPattern (slice q e false p) (slice q e true p) := by
  cases p
  · have hp := matrixPattern_of_weighted_samples hm d hd hdroot (slice q e false false)
      (d • slice q e true false) (by intro t ht; rw [← weightedCard_even]; exact h e false t ht)
    apply matrixPattern_unscale one_ne_zero hd
    simpa using hp
  · have hp := matrixPattern_of_weighted_samples hm d hd hdroot (d • slice q e true true)
      (slice q e false true) (by intro t ht; rw [← weightedCard_odd]; exact h e true t ht)
    apply pattern_swap
    apply matrixPattern_unscale hd one_ne_zero
    simpa using hp

/-- The finite support constraints are conclusions of the complete physical pencil tests. -/
theorem deckSupport_of_samples {m : ℕ} (hm : 3 ≤ m) (d : ℂ) (hd : d ≠ 0)
    (hdroot : (d^2)^m=1) (q : Signature ℂ 4) (h : SafeDeck m d q) :
    DeckSupport (fun w => nonzeroBit (q w)) := by
  intro e p
  obtain ⟨r,hz,hp⟩ := deck_endpoint_pattern hm d hd hdroot q h e p
  refine ⟨r, ?_, ?_⟩
  · intro a b c hn
    apply (nonzeroBit_false _).mpr
    cases a
    · exact hz false b c hn
    · exact hz true b c hn
  · have he : (fun (a b : Bool) => nonzeroBit (q (fill e a p b (b ^^ r)))) =
        (fun a b => nonzeroBit (if a then slice q e true p b (b ^^ r)
          else slice q e false p b (b ^^ r))) := by
      funext a b; cases a <;> rfl
    rwa [he]

/-- The parity/complement atlas is derived, including sparse supports and zero-card patterns. -/
theorem support_atlas_of_samples {m : ℕ} (hm : 3 ≤ m) (d : ℂ) (hd : d ≠ 0)
    (hdroot : (d^2)^m=1) (q : Signature ℂ 4) (hq : q ≠ 0) (h : SafeDeck m d q) :
    ∃ (p : Bool) (selected : PairIndex → Bool), (∃ i, selected i = true) ∧
      ∀ w, q w ≠ 0 ↔ ∃ i, selected i = true ∧
        (w = representative p i ∨ w = complement (representative p i)) := by
  have hne : ∃ w, nonzeroBit (q w) = true := by
    by_contra hn
    apply hq
    funext w
    have hz : q w = 0 := by
      by_contra hh
      exact hn ⟨w, (nonzeroBit_true _).mpr hh⟩
    exact hz
  simpa only [nonzeroBit_true] using classification_pairs
    (deckSupport_of_samples hm d hd hdroot q h) hne

end Holant.Marked.SupportAtlas
