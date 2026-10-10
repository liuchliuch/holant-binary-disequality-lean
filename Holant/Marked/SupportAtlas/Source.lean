import Holant.Marked.SupportAtlas.Reversal
import Holant.Marked.SupportAtlas.ComplementForm

/-! Complete algebraic and actual-realization form of manuscript Lemma 6.27.
Retained-state bookkeeping is replaced by the literal complete physical deck
hypothesis, without assuming any support, parity, or complementary pairing. -/
noncomputable section
namespace Holant.Marked.SupportAtlas
open Holant.Tractable
open Holant.Projective.CyclicQuaternary

def phaseOne (m : ℕ) : Phase m := ⟨1, Roots.one m⟩

theorem reflection_one : S 1 = (Signature.disequality : Mat) := by
  rw [S, R_one, Kernel.mul_equality]

/-- The fixed X dressing is one of the original actual reflection representatives. -/
theorem Representatives.x_transfer {F : SignatureFamily Scalar} {m : ℕ}
    {U : InvertibleKernel} (reps : Representatives F m U) :
    sectorTransfer U (reps.matrix true (phaseOne m)) =
      scale (reps.multiplier true (phaseOne m)) Signature.disequality := by
  simpa only [phaseOne, ↓reduceIte, reflection_one] using reps.transfer true (phaseOne m)

/-- The physical hypotheses are stated in the original current marked group. -/
def NativePhysicalDeck {m : ℕ} (F : SignatureFamily Scalar) (P : Parameters m)
    (q : Signature Scalar 4) (reps : Representatives F m P.basis) : Prop :=
  ∀ (e : Equiv.Perm (Fin 4)) (p : Bool) (t : Phase m),
    physicalCard q e (reps.matrix p t) = 0 ∨
      Kernel.mul (physicalCard q e (reps.matrix p t)) Signature.disequality ∈ P.group

theorem nativePhysicalDeck_iff {m : ℕ} (F : SignatureFamily Scalar) (P : Parameters m)
    (q : Signature Scalar 4) (reps : Representatives F m P.basis) :
    NativePhysicalDeck F P q reps ↔ PhysicalDeck F P q reps := by
  simp only [NativePhysicalDeck, PhysicalDeck, current_group_iff]

/-- **Source Lemma 6.27.** Every ordered physical deck card is actually tested as
zero or current-group safe. The conclusion is the literal complement coefficient
form after an actually realized finite collection of sector-X dressings.
No analytically normalized signature is assumed gadget-realizable. -/
theorem source_marked_support_atlas {m : ℕ} (F : SignatureFamily Scalar)
    (P : Parameters m) (hP : nonstandard P) (q : Signature Scalar 4) (hq : q ≠ 0)
    (hqActual : Gadget.Realizes F .disequality q)
    (reps : Representatives F m P.basis) (hdeck : NativePhysicalDeck F P q reps) :
    ∃ mask : Word,
      Gadget.Realizes F .disequality (dressMask q (reps.matrix true (phaseOne m)) mask) ∧
      dressingMultiplier (reps.multiplier true (phaseOne m)) mask ≠ 0 ∧
      (∀ x : Word,
        P.basis.symm.action (dressMask q (reps.matrix true (phaseOne m)) mask) x =
          dressingMultiplier (reps.multiplier true (phaseOne m)) mask *
            P.basis.symm.action q (xorWord x mask)) ∧
      ComplementForm (P.basis.symm.action (dressMask q (reps.matrix true (phaseOne m)) mask)) := by
  let g := P.basis.symm.action q
  have hg : g ≠ 0 := by
    intro hz
    have hh := P.basis.action_symm_action q
    rw [show P.basis.symm.action q = 0 from hz] at hh
    apply hq
    simpa [InvertibleKernel.action] using hh.symm
  have hnonempty : ∃ w, g w ≠ 0 := by
    by_contra hn
    apply hg
    funext w
    by_contra hw
    exact hn ⟨w,hw⟩
  obtain ⟨mask,hmask⟩ := hnonempty
  have hsamples := safeDeck_of_physical F P hP q reps ((nativePhysicalDeck_iff F P q reps).mp hdeck)
  have hds := deckSupport_of_samples (marked_range P) (delta P : ℂ)
    (by exact_mod_cast delta_ne_zero P) (by exact_mod_cast delta_root P)
    (complexTensor g) hsamples
  have hmaskBit : nonzeroBit (complexTensor g mask) = true := by
    simp [nonzeroBit, complexTensor, hmask]
  have hcomp (w : Word) : g (complement w) = 0 ↔ g w = 0 := by
    have hh : nonzeroBit (complexTensor g (complement w)) = false ↔
        nonzeroBit (complexTensor g w) = false := by rw [complement_eq hds w]
    simpa [complexTensor] using hh
  let c := reps.multiplier true (phaseOne m)
  let B := reps.matrix true (phaseOne m)
  let G := P.basis.symm.action (dressMask q B mask)
  have hc : dressingMultiplier c mask ≠ 0 := dressingMultiplier_ne_zero c
    (reps.multiplier_ne_zero true (phaseOne m)) mask
  have hvalue (x : Word) : G x = dressingMultiplier c mask * g (xorWord x mask) :=
    sector_dressMask P.basis q B c reps.x_transfer mask x
  have hz (x : Word) : G x = 0 ↔ g (xorWord x mask) = 0 := by rw [hvalue]; simp [hc]
  have heven : EvenSupported G := by
    intro x hx
    by_contra hn
    have hw : g (xorWord x mask) ≠ 0 := (hz x).not.mp hn
    have hbit : nonzeroBit (complexTensor g (xorWord x mask)) = true := by
      simp [nonzeroBit, complexTensor, hw]
    have hp := parity_eq hds hbit hmaskBit
    rw [parity_xorWord, ← odd_eq_parity, hx] at hp
    cases hpm : parity mask <;> simp [hpm] at hp
  have hzero : G (fun _ => false) ≠ 0 := by
    rw [hvalue, xorWord_zero]
    exact mul_ne_zero hc hmask
  have hone : G (fun _ => true) ≠ 0 := by
    rw [hvalue, xorWord_one]
    exact mul_ne_zero hc ((hcomp mask).not.mpr hmask)
  have hGcomp (x : Word) : G (complement x) = 0 ↔ G x = 0 := by
    rw [hz, hz, xorWord_complement]
    exact hcomp (xorWord x mask)
  exact ⟨mask, realizes_dressMask F q B hqActual (reps.actual true (phaseOne m)) mask,
    hc, hvalue, complementForm_of_even heven hzero hone hGcomp⟩

end Holant.Marked.SupportAtlas
