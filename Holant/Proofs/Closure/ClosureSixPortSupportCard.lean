import Holant.Proofs.Closure.ClosureSixPortSupport

/-! NEW UNVERIFIED exact noncancellation at the actual I/X phase-one card.
Projection injectivity gives one nonzero summand per output word. The tensor's
full support and original ordered coordinates are retained explicitly. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSixPort
open Holant

@[simp] theorem residualSix_fillSix (e : Equiv.Perm (Fin 6)) (a p : Bool) (x : Word 4) :
    residualSix e (fillSix e a p x) = x := by
  funext i
  simp [residualSix,fillSix]

@[simp] theorem fillSix_pair_parity (e : Equiv.Perm (Fin 6)) (a p : Bool) (x : Word 4) :
    ((fillSix e a p x) (e 0) ^^ (fillSix e a p x) (e 1)) = p := by
  cases a <;> cases p <;> simp [fillSix]

def selectedWords (S : Finset (Word 6)) (e : Equiv.Perm (Fin 6)) (p : Bool) : Finset (Word 6) :=
  S.filter (fun w => (w (e 0) ^^ w (e 1)) = p)

def selectedOutputs (S : Finset (Word 6)) (e : Equiv.Perm (Fin 6)) (p : Bool) : Finset (Word 4) :=
  (selectedWords S e p).image (residualSix e)

/-- One supported lift per residual word excludes cancellation between the
two raw endpoints of the actual phase-one card. -/
theorem phase_one_unique_lift (h : Signature ℂ 6) (S : Finset (Word 6))
    (support : ∀ w, h w ≠ 0 ↔ w ∈ S) (e : Equiv.Perm (Fin 6)) (p : Bool)
    (injective : Set.InjOn (residualSix e) {w | w ∈ selectedWords S e p}) (x : Word 4) :
    sliceSix h e p false x * sliceSix h e p true x = 0 := by
  by_contra hn
  obtain ⟨h0,h1⟩ := mul_ne_zero_iff.mp hn
  have member (a : Bool) (ha : sliceSix h e p a x ≠ 0) :
      fillSix e a p x ∈ selectedWords S e p := by
    exact Finset.mem_filter.mpr ⟨(support _).mp ha,fillSix_pair_parity e a p x⟩
  have equal := injective (member false h0) (member true h1)
    (by simp only [residualSix_fillSix])
  have impossible := congrFun equal (e 0)
  simpa [fillSix] using impossible

/-- EXACT support of the actual ordered I/X contraction at phase one. -/
theorem phase_one_support (h : Signature ℂ 6) (S : Finset (Word 6))
    (support : ∀ w, h w ≠ 0 ↔ w ∈ S) (e : Equiv.Perm (Fin 6)) (p : Bool)
    (injective : Set.InjOn (residualSix e) {w | w ∈ selectedWords S e p}) (x : Word 4) :
    phaseCard h e p 1 x ≠ 0 ↔ x ∈ selectedOutputs S e p := by
  have zeroProduct := phase_one_unique_lift h S support e p injective x
  have member (a : Bool) (ha : sliceSix h e p a x ≠ 0) :
      x ∈ selectedOutputs S e p := by
    apply Finset.mem_image.mpr
    exact ⟨fillSix e a p x,Finset.mem_filter.mpr
      ⟨(support _).mp ha,fillSix_pair_parity e a p x⟩,residualSix_fillSix e a p x⟩
  constructor
  · intro hn
    by_cases h0 : sliceSix h e p false x = 0
    · apply member true
      intro h1
      apply hn
      simp [phaseCard,h0,h1]
    · exact member false h0
  · intro hx
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hs,hp⟩ := Finset.mem_filter.mp hw
    have hn := (support w).mpr hs
    have reconstruct : fillSix e (w (e 0)) p (residualSix e w) = w := by
      rw [←hp]
      exact fillSix_reconstruct e w
    have endpoint : sliceSix h e p (w (e 0)) (residualSix e w) ≠ 0 := by
      unfold sliceSix
      rw [reconstruct]
      exact hn
    have product := phase_one_unique_lift h S support e p injective (residualSix e w)
    cases ha : w (e 0)
    · rw [ha] at endpoint
      have other : sliceSix h e p true (residualSix e w) = 0 :=
        (mul_eq_zero.mp product).resolve_left endpoint
      simpa [phaseCard,other] using endpoint
    · rw [ha] at endpoint
      have other : sliceSix h e p false (residualSix e w) = 0 :=
        (mul_eq_zero.mp product).resolve_right endpoint
      simpa [phaseCard,other] using endpoint

theorem selectedOutputs_card (S : Finset (Word 6)) (e : Equiv.Perm (Fin 6)) (p : Bool)
    (injective : Set.InjOn (residualSix e) {w | w ∈ selectedWords S e p}) :
    (selectedOutputs S e p).card = (selectedWords S e p).card := by
  exact Finset.card_image_iff.mpr injective

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSixPort
