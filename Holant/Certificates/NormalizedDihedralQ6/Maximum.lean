import Holant.Certificates.NormalizedDihedralQ6.Classification
import Holant.Certificates.NormalizedDihedralQ6.SupportNormalization

/-! Semantic maximal injective projection, its exact covariance, and lifting the
canonical certificate to every original labelled support without re-enumeration. -/
namespace Holant.Certificates.NormalizedDihedralQ6

/-- A largest injective parity projection has exactly n distinct four-port words. -/
def HasMaximum (S : Support) (n : ℕ) : Prop :=
  (∃ p γ, p.1 ≠ p.2 ∧ injectiveProjection S p γ ∧ (projected S p γ).card = n) ∧
    ∀ p : Pair, p.1 ≠ p.2 → ∀ γ, injectiveProjection S p γ → (projected S p γ).card ≤ n

theorem HasMaximum.unique {S : Support} {m n : ℕ} (hm : HasMaximum S m) (hn : HasMaximum S n) : m = n := by
  rcases hm.1 with ⟨p,γ,hp,hi,hc⟩
  rcases hn.1 with ⟨q,δ,hq,hj,hd⟩
  have hmn := hn.2 p hp γ hi
  have hnm := hm.2 q hq δ hj
  omega

private theorem parity_twist_twice (a b c : Bool) : ((a ^^ b ^^ c) ^^ b ^^ c) = a := by
  cases a <;> cases b <;> cases c <;> decide

/-- For an injective slice, coordinate normalization preserves the exact image size. -/
theorem projected_card_transform_of_injective (π : Equiv.Perm Port) (δ : Word) (S : Support)
    (p : Pair) (γ : Bool) (hi : injectiveProjection S (π p.1,π p.2) γ) :
    (projected (transform π δ S) p (γ ^^ δ p.1 ^^ δ p.2)).card =
      (projected S (π p.1,π p.2) γ).card := by
  have ht := (injectiveProjection_transform_iff π δ S p γ).mpr hi
  rw [(injectiveProjection_iff _ _ _).mp ht, slice_card_transform]
  exact ((injectiveProjection_iff _ _ _).mp hi).symm

/-- Forward covariance transports both an attaining pair and every competing pair. -/
theorem HasMaximum.transform {S : Support} {n : ℕ} (h : HasMaximum S n)
    (π : Equiv.Perm Port) (δ : Word) : HasMaximum (transform π δ S) n := by
  constructor
  · rcases h.1 with ⟨p,γ,hp,hi,hc⟩
    let q : Pair := (π.symm p.1,π.symm p.2)
    have hq : q.1 ≠ q.2 := fun he => hp (π.symm.injective he)
    have hi' : injectiveProjection S (π q.1,π q.2) γ := by simpa [q] using hi
    have ht := (injectiveProjection_transform_iff π δ S q γ).mpr hi'
    refine ⟨q,γ ^^ δ q.1 ^^ δ q.2,hq,ht,?_⟩
    have hh := projected_card_transform_of_injective π δ S q γ hi'
    simpa [q] using hh.trans (by simpa [q] using hc)
  · intro p hp γ hi
    let η : Bool := γ ^^ δ p.1 ^^ δ p.2
    have hη : (η ^^ δ p.1 ^^ δ p.2) = γ := parity_twist_twice _ _ _
    have hi' : injectiveProjection S (π p.1,π p.2) η := by
      apply (injectiveProjection_transform_iff π δ S p η).mp
      simpa only [hη] using hi
    have hp' : π p.1 ≠ π p.2 := fun he => hp (π.injective he)
    have hh := projected_card_transform_of_injective π δ S p η hi'
    rw [hη] at hh
    exact hh.trans_le (h.2 _ hp' η hi')

/-- Maximality is invariant under every literal port permutation and independent bit flip. -/
theorem hasMaximum_transform_iff (π : Equiv.Perm Port) (δ : Word) (S : Support) (n : ℕ) :
    HasMaximum (transform π δ S) n ↔ HasMaximum S n := by
  constructor
  · intro h
    have hh := h.transform π.symm (fun i => δ (π.symm i))
    rwa [transform_inverse] at hh
  · intro h
    exact h.transform π δ

/-- A literal table entry gives the semantic maximum, not just one valid projection. -/
theorem canonical_hasMaximum (d : Sector) (p : Pair) (γ : Bool) (n : ℕ)
    (hw : printedWitness d = some (p,γ,n)) : HasMaximum (canonicalSupport d) n := by
  have h := printed_witness d p γ n hw
  refine ⟨⟨p,γ,ne_of_lt h.1,h.2.2.1,h.2.2.2.2⟩,?_⟩
  intro q hq δ hi
  rw [(injectiveProjection_iff _ _ _).mp hi]
  exact printed_maximality d (p,γ,n) hw q hq δ hi

/-- Exact semantic classification of the canonical nonmatching maximum. -/
theorem canonical_maximum_iff (d : Sector) (n : ℕ) :
    (¬ matchingCoset (canonicalSupport d) ∧ HasMaximum (canonicalSupport d) n) ↔
      ∃ p γ, printedWitness d = some (p,γ,n) := by
  constructor
  · rintro ⟨hn,hm⟩
    cases hw : printedWitness d with
    | none => exact False.elim (hn ((canonical_matching_iff d).mpr ((printed_none_iff d).mp hw)))
    | some w =>
      rcases w with ⟨p,γ,m⟩
      have he := (canonical_hasMaximum d p γ m hw).unique hm
      subst m
      exact ⟨p,γ,rfl⟩
  · rintro ⟨p,γ,hw⟩
    refine ⟨?_,canonical_hasMaximum d p γ n hw⟩
    intro hm
    have hn := (printed_none_iff d).mpr ((canonical_matching_iff d).mp hm)
    rw [hw] at hn
    contradiction

/-- Matching status of every original choice is exactly the normalized printed M entry. -/
theorem original_matching_iff (d₀ d₁ : Sector) :
    matchingCoset (support d₀ d₁) ↔ printedWitness (normalizeOdd d₀ d₁) = none := by
  have h := matchingCoset_transform_iff (normalPerm d₀.1) (normalFlip d₀) (support d₀ d₁)
  rw [normalize_support,canonical_matching_iff] at h
  exact h.symm.trans (printed_none_iff _).symm

/-- The largest projection for every original nonmatching support is the normalized printed size. -/
theorem original_maximum_iff (d₀ d₁ : Sector) (n : ℕ) :
    (¬ matchingCoset (support d₀ d₁) ∧ HasMaximum (support d₀ d₁) n) ↔
      ∃ p γ, printedWitness (normalizeOdd d₀ d₁) = some (p,γ,n) := by
  have hm := matchingCoset_transform_iff (normalPerm d₀.1) (normalFlip d₀) (support d₀ d₁)
  have hx := hasMaximum_transform_iff (normalPerm d₀.1) (normalFlip d₀) (support d₀ d₁) n
  rw [normalize_support] at hm hx
  rw [← hm,← hx]
  exact canonical_maximum_iff _ _

end Holant.Certificates.NormalizedDihedralQ6
