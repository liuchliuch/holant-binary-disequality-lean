import Holant.Proofs.Hardness.GeneralEOPinnedDescentOperations

/-! A finite, coefficient-preserving descent choice for three supported words.
The output is an actual network formed using native X and paired pins; the
choice is obtained solely from the source coefficients. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPinnedDescentCore
open Holant
namespace O
export GeneralEOPinnedDescentOperations
  (word word_weight pinned pinned_denote signed signed_denote)
end O
set_option backward.isDefEq.respectTransparency false
variable {K : Type*} [Field K] {W : Type*} {n : ℕ}

/-- The complete list of physical descent operations. -/
inductive Branch where
  | pin10 | pin01 | loop | signedAlpha | signedBeta
  deriving DecidableEq, Repr, Fintype

/-- All decisions inspect finitely many coefficients of the two prefix slices. -/
def choice (p q : W → K) (a b c : W) : Branch := by
  classical
  exact if p c ≠ 0 then .pin10 else
  if q a ≠ 0 ∧ q b ≠ 0 then .pin01 else
  if p a + q a = 0 then .signedAlpha else
  if p b + q b = 0 then .signedBeta else .loop

/-- Exact denotations, including the coefficient supplied by the second copy. -/
def value (p q : W → K) (a b : W) : Branch → W → K
  | .pin10, x => p x
  | .pin01, x => q x
  | .loop, x => q x + p x
  | .signedAlpha, x => p a * (q x - p x)
  | .signedBeta, x => p b * (q x - p x)

/-- The unnormalized cancellation repair retains its factor of two. -/
theorem cancellation_value (u v : K) (hc : u + v = 0) :
    u * (v - u) = -2 * u ^ 2 := by
  linear_combination u * hc

private theorem cancellation_other_ne_zero {u v : K} (hu : u ≠ 0)
    (hc : u + v = 0) : v ≠ 0 := by
  intro hv
  exact hu (by simpa [hv] using hc)

private theorem cancellation_value_ne_zero [CharZero K] {u v : K}
    (hu : u ≠ 0) (hc : u + v = 0) : u * (v - u) ≠ 0 := by
  rw [cancellation_value u v hc]
  exact mul_ne_zero (neg_ne_zero.mpr (by norm_num)) (pow_ne_zero _ hu)

/-- The branch is selected without any classifier, hardness, or recursion premise. -/
theorem choice_supported [CharZero K] (p q : W → K) (a b c : W)
    (ha : p a ≠ 0) (hb : p b ≠ 0) (hc : q c ≠ 0) :
    value p q a b (choice p q a b c) a ≠ 0 ∧
    value p q a b (choice p q a b c) b ≠ 0 ∧
    value p q a b (choice p q a b c) c ≠ 0 := by
  classical
  unfold choice
  split_ifs with hpc hpin hcancelA hcancelB
  · exact ⟨ha, hb, hpc⟩
  · exact ⟨hpin.1, hpin.2, hc⟩
  · have hpc0 : p c = 0 := not_ne_iff.mp hpc
    have hqa : q a ≠ 0 := cancellation_other_ne_zero ha hcancelA
    have hqb : q b = 0 := by
      by_contra hn
      exact hpin ⟨hqa, hn⟩
    dsimp [value]
    refine ⟨cancellation_value_ne_zero ha hcancelA, mul_ne_zero ha ?_, mul_ne_zero ha ?_⟩
    · simpa [hqb] using neg_ne_zero.mpr hb
    · simpa [hpc0] using hc
  · have hpc0 : p c = 0 := not_ne_iff.mp hpc
    have hqb : q b ≠ 0 := cancellation_other_ne_zero hb hcancelB
    have hqa : q a = 0 := by
      by_contra hn
      exact hpin ⟨hn, hqb⟩
    dsimp [value]
    refine ⟨mul_ne_zero hb ?_, cancellation_value_ne_zero hb hcancelB, mul_ne_zero hb ?_⟩
    · simpa [hqa] using neg_ne_zero.mpr ha
    · simpa [hpc0] using hc
  · have hpc0 : p c = 0 := not_ne_iff.mp hpc
    exact ⟨by simpa [value, add_comm] using hcancelA,
      by simpa [value, add_comm] using hcancelB, by simpa [value, hpc0] using hc⟩

/-- Each signed branch carries the cancellation equation needed by its cap. -/
theorem choice_cancellation (p q : W → K) (a b c : W) :
    (choice p q a b c = .signedAlpha → p a + q a = 0) ∧
    (choice p q a b c = .signedBeta → p b + q b = 0) := by
  classical
  unfold choice
  split_ifs <;> simp_all

/-- Any common zero of the two slices remains zero under every branch. -/
theorem value_zero (p q : W → K) (a b d : W) (hp : p d = 0) (hq : q d = 0)
    (j : Branch) : value p q a b j d = 0 := by
  cases j <;> simp [value, hp, hq]

/-- A supported complementary-prefix extension supplies the balance witness
needed to extract the signed cap from a second actual source copy. -/
theorem tail_balanced (S : Network K (n+2)) (he : Signature.CentralSupport S.denote)
    (u : Bool) (x : Fin n → Bool) (hx : S.denote (O.word u (!u) x) ≠ 0) :
    2 * weight x = n := by
  have h : 2 * weight (O.word u (!u) x) = n+2 := by
    by_contra hn
    exact hx (he _ hn)
  rw [O.word_weight] at h
  cases u <;> simp only [Bool.not_false, Bool.not_true, ite_true,
    Bool.false_eq_true, ite_false] at h <;> omega

def slice10 (S : Network K (n+2)) (x : Fin n → Bool) : K := S.denote (O.word true false x)
def slice01 (S : Network K (n+2)) (x : Fin n → Bool) : K := S.denote (O.word false true x)

/-- Every constructor is physical: one paired pin, a native loop, or a second-copy cap. -/
def branchNetwork (S : Network K (n+2)) (he : Signature.CentralSupport S.denote)
    (a b : Fin n → Bool) (ha : slice10 S a ≠ 0) (hb : slice10 S b ≠ 0) : Branch → Network K n
  | .pin10 => O.pinned S true
  | .pin01 => O.pinned S false
  | .loop => S.contract Signature.disequality
  | .signedAlpha => O.signed S a (tail_balanced S he true a ha)
  | .signedBeta => O.signed S b (tail_balanced S he true b hb)

/-- The output is the selected physical network, with balance proved internally. -/
def network (S : Network K (n+2)) (he : Signature.CentralSupport S.denote)
    (a b c : Fin n → Bool) (ha : slice10 S a ≠ 0) (hb : slice10 S b ≠ 0) : Network K n :=
  branchNetwork S he a b ha hb (choice (slice10 S) (slice01 S) a b c)

/-- Exact output semantics, with no normalization or suppressed multiplicity. -/
theorem network_denote (S : Network K (n+2)) (he : Signature.CentralSupport S.denote)
    (a b c : Fin n → Bool) (ha : slice10 S a ≠ 0) (hb : slice10 S b ≠ 0) (x : Fin n → Bool) :
    (network S he a b c ha hb).denote x =
      value (slice10 S) (slice01 S) a b (choice (slice10 S) (slice01 S) a b c) x := by
  have hh := choice_cancellation (slice10 S) (slice01 S) a b c
  unfold network
  generalize hj : choice (slice10 S) (slice01 S) a b c = j at *
  cases j
  · exact O.pinned_denote S true x
  · exact O.pinned_denote S false x
  · exact Network.denote_contract_disequality S x
  · exact O.signed_denote S he a (tail_balanced S he true a ha) (hh.1 rfl) x
  · exact O.signed_denote S he b (tail_balanced S he true b hb) (hh.2 rfl) x

/-- The three designated central words survive the finite descent. -/
theorem supported [CharZero K] (S : Network K (n+2)) (he : Signature.CentralSupport S.denote)
    (a b c : Fin n → Bool) (ha : slice10 S a ≠ 0) (hb : slice10 S b ≠ 0) (hc : slice01 S c ≠ 0) :
    (network S he a b c ha hb).denote a ≠ 0 ∧
    (network S he a b c ha hb).denote b ≠ 0 ∧
    (network S he a b c ha hb).denote c ≠ 0 := by
  simp only [network_denote]
  exact choice_supported (slice10 S) (slice01 S) a b c ha hb hc

/-- A missing word stays missing whenever both its complementary extensions vanish. -/
theorem hole (S : Network K (n+2)) (he : Signature.CentralSupport S.denote)
    (a b c : Fin n → Bool) (ha : slice10 S a ≠ 0) (hb : slice10 S b ≠ 0)
    (d : Fin n → Bool) (hd10 : slice10 S d = 0) (hd01 : slice01 S d = 0) :
    (network S he a b c ha hb).denote d = 0 := by
  rw [network_denote]
  exact value_zero _ _ a b d hd10 hd01 _

/-- No off-central word is introduced by the selected physical descent. -/
theorem central (S : Network K (n+2)) (he : Signature.CentralSupport S.denote)
    (a b c : Fin n → Bool) (ha : slice10 S a ≠ 0) (hb : slice10 S b ≠ 0) :
    Signature.CentralSupport (network S he a b c ha hb).denote := by
  intro x hx
  apply hole S he a b c ha hb x
  · apply he
    rw [O.word_weight]
    simp only [ite_true, Bool.false_eq_true, ite_false]
    omega
  · apply he
    rw [O.word_weight]
    simp only [ite_true, Bool.false_eq_true, ite_false]
    omega

/-- The actual signed cap evaluates to the full unnormalized factor at its witness. -/
theorem signed_witness (S : Network K (n+2)) (he : Signature.CentralSupport S.denote)
    (w : Fin n → Bool) (hw : slice10 S w ≠ 0) (hc : slice10 S w + slice01 S w = 0) :
    (O.signed S w (tail_balanced S he true w hw)).denote w = -2 * (slice10 S w)^2 := by
  rw [O.signed_denote S he w (tail_balanced S he true w hw) hc]
  exact cancellation_value _ _ hc

/-- The selected alpha repair keeps the same unnormalized witness value. -/
theorem network_signedAlpha_witness (S : Network K (n+2))
    (he : Signature.CentralSupport S.denote) (a b c : Fin n → Bool)
    (ha : slice10 S a ≠ 0) (hb : slice10 S b ≠ 0)
    (hj : choice (slice10 S) (slice01 S) a b c = .signedAlpha) :
    (network S he a b c ha hb).denote a = -2 * (slice10 S a)^2 := by
  rw [network_denote, hj]
  exact cancellation_value _ _ ((choice_cancellation _ _ a b c).1 hj)

/-- The selected beta repair keeps the same unnormalized witness value. -/
theorem network_signedBeta_witness (S : Network K (n+2))
    (he : Signature.CentralSupport S.denote) (a b c : Fin n → Bool)
    (ha : slice10 S a ≠ 0) (hb : slice10 S b ≠ 0)
    (hj : choice (slice10 S) (slice01 S) a b c = .signedBeta) :
    (network S he a b c ha hb).denote b = -2 * (slice10 S b)^2 := by
  rw [network_denote, hj]
  exact cancellation_value _ _ ((choice_cancellation _ _ a b c).2 hj)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPinnedDescentCore
