import Holant.Tractable.Criteria

/-! Structural reduction of the full shared-sign/shared-class EO criterion.
The two choices are independent. Consequently a failure is already witnessed
by at most two original signatures, even when every singleton is tractable.
No complexity conclusion is assumed or asserted in this module. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EONegativeWitness
open Holant Holant.Tractable

/-- The support half of the literal criterion, for one fixed sign. -/
def Supports (sign : EOSign) (g : AnySignature AlgebraicComplex) : Prop :=
  ∀ a b c, g.2 a ≠ 0 → g.2 b ≠ 0 → g.2 c ≠ 0 →
    g.2 (tripleXor a b c) ≠ 0 ∨ 0 < sign.value * Holant.charge (tripleXor a b c)

/-- The pairing half, for one fixed class and all original ordered pairings. -/
def Pairings (C : EOClass) (g : AnySignature AlgebraicComplex) : Prop :=
  ∀ p : OrientedPerfectPairing g.1, C.Holds (p.restrict g.2)

/-- These are two independent binary choices, rather than four arbitrary
allowed profiles. This factorization is what makes the two-witness bound valid. -/
theorem criterion_iff {G : SignatureFamily AlgebraicComplex} (hfin : G.Finite)
    (heo : ∀ g ∈ G, IsEO g) : EOTract G ↔
    ((∀ g ∈ G, Supports .positive g) ∨ (∀ g ∈ G, Supports .negative g)) ∧
    ((∀ g ∈ G, Pairings .affine g) ∨ (∀ g ∈ G, Pairings .product g)) := by
  constructor
  · rintro ⟨_, _, sign, C, hs, hc⟩
    constructor
    · cases sign with
      | positive => exact Or.inl hs
      | negative => exact Or.inr hs
    · cases C with
      | affine => exact Or.inl hc
      | product => exact Or.inr hc
  · rintro ⟨hs, hc⟩
    rcases hs with hs | hs <;> rcases hc with hc | hc
    · exact ⟨hfin, heo, .positive, .affine, hs, hc⟩
    · exact ⟨hfin, heo, .positive, .product, hs, hc⟩
    · exact ⟨hfin, heo, .negative, .affine, hs, hc⟩
    · exact ⟨hfin, heo, .negative, .product, hs, hc⟩

/-- Each disjunct records the actual incompatible component of EOTract. -/
def Obstruction (g h : AnySignature AlgebraicComplex) : Prop :=
  (¬Supports .positive g ∧ ¬Supports .negative h) ∨
  (¬Pairings .affine g ∧ ¬Pairings .product h)

/-- Full-family failure selects original witnesses; they need not be distinct. -/
theorem exists_pair {G : SignatureFamily AlgebraicComplex} (hfin : G.Finite)
    (heo : ∀ g ∈ G, IsEO g) (hbad : ¬EOTract G) :
    ∃ g ∈ G, ∃ h ∈ G, Obstruction g h := by
  classical
  have hf := (criterion_iff hfin heo).not.mp hbad
  rcases not_and_or.mp hf with hs | hc
  · push_neg at hs
    obtain ⟨g, hg, hp⟩ := hs.1
    obtain ⟨h, hh, hn⟩ := hs.2
    exact ⟨g, hg, h, hh, Or.inl ⟨hp, hn⟩⟩
  · push_neg at hc
    obtain ⟨g, hg, ha⟩ := hc.1
    obtain ⟨h, hh, hp⟩ := hc.2
    exact ⟨g, hg, h, hh, Or.inr ⟨ha, hp⟩⟩

/-- Either witness blocks the same outer choice in the full predicate. -/
theorem pair_not_tract {g h : AnySignature AlgebraicComplex} (ho : Obstruction g h) :
    ¬EOTract {g, h} := by
  rintro ⟨_, _, sign, C, hs, hc⟩
  rcases ho with ho | ho
  · cases sign with
    | positive => exact ho.1 (hs g (by simp))
    | negative => exact ho.2 (hs h (by simp))
  · cases C with
    | affine => exact ho.1 (hc g (by simp))
    | product => exact ho.2 (hc h (by simp))

/-- The support obstruction includes actual supported words and a missing
triple xor on the forbidden weak side, including charge zero. -/
theorem support_failure {sign : EOSign} {g : AnySignature AlgebraicComplex}
    (h : ¬Supports sign g) : ∃ a b c, g.2 a ≠ 0 ∧ g.2 b ≠ 0 ∧ g.2 c ≠ 0 ∧
      g.2 (tripleXor a b c) = 0 ∧ sign.value * Holant.charge (tripleXor a b c) ≤ 0 := by
  classical
  unfold Supports at h
  push_neg at h
  exact h

/-- The class obstruction contains an actual oriented perfect pairing. -/
theorem pairing_failure {C : EOClass} {g : AnySignature AlgebraicComplex}
    (h : ¬Pairings C g) : ∃ p : OrientedPerfectPairing g.1, ¬C.Holds (p.restrict g.2) := by
  classical
  exact not_forall.mp h

/-- Equivalent universal pair criterion, with no pairwise weakening. -/
theorem all_pairs_iff {G : SignatureFamily AlgebraicComplex} (hfin : G.Finite)
    (heo : ∀ g ∈ G, IsEO g) : EOTract G ↔ ∀ g ∈ G, ∀ h ∈ G, EOTract {g, h} := by
  constructor
  · rintro ⟨_, _, sign, C, hs, hc⟩ g hg h hh
    refine ⟨by simp, ?_, sign, C, ?_, ?_⟩
    · intro k hk
      rcases Set.mem_insert_iff.mp hk with rfl | hk
      · exact heo _ hg
      · rcases Set.mem_singleton_iff.mp hk with rfl
        exact heo _ hh
    · intro k hk
      rcases Set.mem_insert_iff.mp hk with rfl | hk
      · exact hs _ hg
      · rcases Set.mem_singleton_iff.mp hk with rfl
        exact hs _ hh
    · intro k hk
      rcases Set.mem_insert_iff.mp hk with rfl | hk
      · exact hc _ hg
      · rcases Set.mem_singleton_iff.mp hk with rfl
        exact hc _ hh
  · intro hall
    by_contra hn
    obtain ⟨g, hg, h, hh, ho⟩ := exists_pair hfin heo hn
    exact pair_not_tract ho (hall g hg h hh)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EONegativeWitness
