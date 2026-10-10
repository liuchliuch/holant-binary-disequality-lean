import Holant.Proofs.Closure.ClosureSixPortGauge

/-! NEW UNVERIFIED original-coordinate C/C support obstruction. The table's
permutation/bit-flip witness is applied to an actual original phase-one card,
with exact injective lifts and nonzero coefficients. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSixPort
open Holant

theorem gauge_normalized_atlas_forces_matching {m : ℕ} (h : Signature ℂ 6)
    (deck : OrderedRootDeck m h) (edge : Fin 6) (a b o : Bool)
    (e : Equiv.Perm (Fin 6)) (flip : Word 6)
    (support : ∀ w, h w ≠ 0 ↔ w ∈ (flatSupport edge a b o).image (gaugeWord e flip)) :
    edge=0 ∧ a=false ∧ b=true := by
  by_contra notMatching
  obtain ⟨order,p,T,card,supported⟩ :=
    gauge_normalized_actual_card_support edge a b o notMatching e flip h support
  have same : ClosureRootPencil.support (phaseCard h order p 1) = T := by
    ext x
    simp only [ClosureRootPencil.support,Finset.mem_filter,Finset.mem_univ,true_and]
    exact supported x
  rcases deck order p 1 (one_pow m) with zero | matching
  · have empty : T = ∅ := by
      rw [←same,zero]
      ext x
      simp [ClosureRootPencil.support]
    rw [empty] at card
    simp at card
  · have four := rootMatching_four_support _ matching
    rw [same] at four
    omega

/-- A matching-coset exception exposes a zero sector in the ORIGINAL
coordinates. Its parity tag records the exact two normalization flips. -/
theorem gauge_matching_zero_sector (h : Signature ℂ 6) (o : Bool)
    (e : Equiv.Perm (Fin 6)) (flip : Word 6)
    (support : ∀ w, h w ≠ 0 ↔ w ∈ (nativeMatchingSupport o).image (gaugeWord e flip)) :
    ∃ order : Equiv.Perm (Fin 6), ∃ p : Bool, ZeroSector h order p := by
  let j : Fin 6 := if o then 5 else 4
  have distinct : (0 : Fin 6) ≠ j := by cases o <;> decide
  let order := pairOrder 0 j
  have first : order 0 = 0 := pairOrder_first _ _ distinct
  have second : order 1 = j := pairOrder_second _ _ distinct
  let actualOrder := order.trans e
  let actualParity := !(pairFlip order flip)
  have zero (a : Bool) : sliceSix h actualOrder actualParity a = 0 := by
    funext x
    by_contra hn
    have member := (support (fillSix actualOrder a actualParity x)).mp hn
    obtain ⟨w,hw,equal⟩ := Finset.mem_image.mp member
    have matched := (Finset.mem_filter.mp hw).2.1
    change w 0 = w j at matched
    have canonicalParity : (w (order 0) ^^ w (order 1))=false := by
      rw [first,second,matched,Bool.xor_self]
    have actual := gauge_pair_parity e order flip w
    rw [canonicalParity,Bool.false_xor,equal] at actual
    have pair := fillSix_pair_parity actualOrder a actualParity x
    rw [pair] at actual
    exact Bool.not_ne_self _ actual
  exact ⟨actualOrder,actualParity,zero false,zero true⟩

/-- No invariant transformed-deck premise is used: all cards below are the
literal ordered cards of h itself, after exact support-coordinate transport. -/
theorem gauge_four_flat_has_zero_sector {m : ℕ} (h : Signature ℂ 6)
    (deck : OrderedRootDeck m h) (edge : Fin 6) (a b o : Bool)
    (e : Equiv.Perm (Fin 6)) (flip : Word 6)
    (support : ∀ w, h w ≠ 0 ↔ w ∈ (flatSupport edge a b o).image (gaugeWord e flip)) :
    ∃ order : Equiv.Perm (Fin 6), ∃ p : Bool, ZeroSector h order p := by
  have matching := gauge_normalized_atlas_forces_matching h deck edge a b o e flip support
  rcases matching with ⟨rfl,rfl,rfl⟩
  have equality : flatSupport 0 false true o = nativeMatchingSupport o := by cases o <;> decide
  apply gauge_matching_zero_sector h o e flip
  intro w
  simpa only [equality] using support w

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSixPort
