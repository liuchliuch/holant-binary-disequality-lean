import Holant.Proofs.Hardness.GeneralEOCentralHolePatternsSix

/-! The complete coordinate alternative for a central support hole: one of the
two genuine reduction prefixes, arity four, or the exact six-port normal form. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOCentralHolePatterns
open Holant Holant.Tractable
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} (p : OrientedPerfectPairing n) (a b c : Fin n → Bool)

/-- Three different compatible words require at least two physical pairs. -/
theorem four_le_of_distinct (ha : L.Compatible p a) (hb : L.Compatible p b)
    (hc : L.Compatible p c) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : 4 ≤ n := by
  let w : Fin 3 → (Fin n → Bool) := ![a,b,c]
  have hw : Function.Injective w := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [w]
  have hp : ∀ t, L.Compatible p (w t) := by
    intro t
    fin_cases t
    · exact ha
    · exact hb
    · exact hc
  let z : Fin 3 → (Fin p.count → Bool) :=
    fun t => Holant.LocalDrafts.Tractability.EOEvaluation.PairLift.compress p (w t)
  have hz : Function.Injective z := by
    intro i j hij
    apply hw
    rw [←Holant.LocalDrafts.Tractability.EOEvaluation.PairLift.word_compress p (w i) (hp i),
      ←Holant.LocalDrafts.Tractability.EOEvaluation.PairLift.word_compress p (w j) (hp j)]
    exact congrArg p.word hij
  have hcard := Fintype.card_le_of_injective z hz
  have hcount : 2 ≤ p.count := by
    by_contra h
    have h' : p.count = 0 ∨ p.count = 1 := by omega
    rcases h' with h' | h' <;> simp [h'] at hcard
  have hn := twice_count p
  omega

/-- The supported inputs of a missing triple xor are necessarily distinct. -/
theorem hole_distinct {K : Type*} [Zero K] (f : Signature K n)
    (ha : f a ≠ 0) (hb : f b ≠ 0) (hc : f c ≠ 0) (hz : f (tripleXor a b c) = 0) :
    a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  refine ⟨?_,?_,?_⟩
  · intro h
    have hx : tripleXor a b c = c := by
      funext t
      simp [tripleXor,h]
    exact hc (hx ▸ hz)
  · intro h
    have hx : tripleXor a b c = b := by
      funext t
      simp only [tripleXor,h]
      cases c t <;> cases b t <;> rfl
    exact hb (hx ▸ hz)
  · intro h
    have hx : tripleXor a b c = a := by
      funext t
      simp only [tripleXor,h]
      cases a t <;> cases c t <;> rfl
    exact ha (hx ▸ hz)

/-- The finite combinatorial exhaustion, including the actual six-port words. -/
theorem terminal_partition (ha : L.Compatible p a) (hb : L.Compatible p b)
    (hc : L.Compatible p c) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (∃ (h : 2 ≤ n) (e : Equiv.Perm (Fin n)),
      ConstantColumns a b c (fun t => e (Fin.castLE h t))) ∨
    (∃ (h : 4 ≤ n) (e : Equiv.Perm (Fin n)),
      RepeatedColumns10 a b c (fun t => e (Fin.castLE h t))) ∨
    n = 4 ∨
    (∃ e : Fin 6 ≃ Fin n,
      a ∘ e = sixFirst ∧ b ∘ e = sixSecond ∧ c ∘ e = sixThird ∧
      (tripleXor a b c) ∘ e = sixHole) := by
  classical
  by_cases hz : ∃ k, key p a b c k = (false,false)
  · obtain ⟨k,hk⟩ := hz
    obtain ⟨i,j,hij,hai,hbi,hci,haj,hbj,hcj⟩ := constant_coordinates p a b c ha hb hc k hk
    exact Or.inl (constant_prefix_permutation a b c i j hij hai hbi hci haj hbj hcj)
  have hzero : ∀ k, key p a b c k ≠ (false,false) := by simpa using hz
  right
  by_cases hi : Function.Injective (key p a b c)
  · right
    have hs := small_of_no_constant_no_repeat p a b c hzero hi
    have hl := four_le_of_distinct p a b c ha hb hc hab hac hbc
    have hp := twice_count p
    have hn : n = 4 ∨ n = 6 := by omega
    rcases hn with hn | hn
    · exact Or.inl hn
    · exact Or.inr (six_normal_form p a b c hn ha hb hc hzero hi)
  · left
    simp only [Function.Injective,not_forall] at hi
    obtain ⟨i,j,hk,hij⟩ := hi
    obtain ⟨v,hv,hcols⟩ := repeated_coordinates p a b c ha hb hc i j hij hk (hzero i)
    exact repeated_prefix_permutation a b c v hv hcols

/-- Every arbitrary-support central hole has a physical reduction prefix or
one of the two exact base arities. No endpoint, successful descent, pairing
restriction, or hardness conclusion is assumed. -/
theorem central_terminal_partition (f : Signature AlgebraicComplex n)
    (he : Signature.CentralSupport f) (ha : f a ≠ 0) (hb : f b ≠ 0) (hc : f c ≠ 0)
    (hz : f (tripleXor a b c) = 0) (hd : charge (tripleXor a b c) = 0) :
    (∃ (h : 2 ≤ n) (e : Equiv.Perm (Fin n)),
      ConstantColumns a b c (fun t => e (Fin.castLE h t))) ∨
    (∃ (h : 4 ≤ n) (e : Equiv.Perm (Fin n)),
      RepeatedColumns10 a b c (fun t => e (Fin.castLE h t))) ∨
    n = 4 ∨
    (∃ e : Fin 6 ≃ Fin n,
      a ∘ e = sixFirst ∧ b ∘ e = sixSecond ∧ c ∘ e = sixThird ∧
      (tripleXor a b c) ∘ e = sixHole) := by
  let p := GeneralEONegativePairing.pairing f he ha hb hc hd
  have hp0 : L.Compatible p a := by
    simpa [p] using GeneralEONegativePairing.compatible f he ha hb hc hd (false,false)
  have hp1 : L.Compatible p b := by
    simpa [p] using GeneralEONegativePairing.compatible f he ha hb hc hd (true,false)
  have hp2 : L.Compatible p c := by
    simpa [p] using GeneralEONegativePairing.compatible f he ha hb hc hd (false,true)
  obtain ⟨hab,hac,hbc⟩ := hole_distinct a b c f ha hb hc hz
  exact terminal_partition p a b c hp0 hp1 hp2 hab hac hbc

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOCentralHolePatterns
