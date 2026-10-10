import Holant.ReedMuller.FlatNetwork.GenerationProgram

/-! Constructive extraction and reduction of a proper self-dual codeword.
The number of weight-four transvections is exactly half the removed weight. -/
namespace Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.LowArity
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

private theorem reduceWeightAux (w : ℕ) :
    ∀ (D : BinaryCode n), SelfDual D → ∀ x : BinaryVector n, x ∈ D →
      binaryWeight x = w → 0 < w → w < n →
      ∃ (p : GenerationProgram n) (z : BinaryVector n),
        2*p.length + 2 = w ∧ z ∈ p.run D ∧ binaryWeight z = 2 := by
  induction w using Nat.strong_induction_on with
  | h w ih =>
    intro D hD x hx hw hp hz
    by_cases htwo : w = 2
    · exact ⟨[], x, by simp [htwo], hx, hw.trans htwo⟩
    have he := selfDual_weight_even D hD x hx
    rw [hw] at he
    obtain ⟨a, ha⟩ := he
    have hlarge : 2 < binaryWeight x := by omega
    obtain ⟨s, hs, his, hdrop⟩ := exists_weightFour_reduction x hlarge (by omega)
    have hnew : transvection s x ∈ transvectionCode s D := ⟨x, hx, rfl⟩
    have hself := transvectionCode_selfDual s his D hD
    have hpositive : 0 < binaryWeight (transvection s x) := by omega
    have hsmall : binaryWeight (transvection s x) < w := by omega
    obtain ⟨p, z, hlen, hmem, hwt⟩ := ih _ hsmall (transvectionCode s D) hself
      (transvection s x) hnew rfl hpositive (by omega)
    refine ⟨p ++ [.tau s hs], z, ?_, ?_, hwt⟩
    · simp only [List.length_append, List.length_singleton]
      omega
    · simpa only [GenerationProgram.run_append, GenerationProgram.run_cons,
        GenerationProgram.run_nil, GenerationGate.applyCode] using hmem

/-- Any nonzero, nonconstant word of a self-dual code can be reduced to
weight two by exactly `(weight - 2) / 2` genuine weight-four gates. -/
theorem exists_weightTwo_reduction (D : BinaryCode n) (hD : SelfDual D)
    (x : BinaryVector n) (hx : x ∈ D) (h0 : x ≠ 0) (h1 : x ≠ ones n) :
    ∃ (p : GenerationProgram n) (z : BinaryVector n),
      2*p.length + 2 = binaryWeight x ∧ z ∈ p.run D ∧ binaryWeight z = 2 :=
  reduceWeightAux (binaryWeight x) D hD x hx rfl
    ((binaryWeight_pos_iff x).mpr h0) ((binaryWeight_lt_iff x).mpr h1)

/-- If the first adjacent pair is missing, self-duality itself supplies a
proper nonzero word. No dimension or basis choice is assumed. -/
theorem exists_proper_word_of_pair_missing (D : BinaryCode (n+2)) (hD : SelfDual D)
    (hp : pairWord n ∉ D) :
    ∃ x : BinaryVector (n+2), x ∈ D ∧ x ≠ 0 ∧ x ≠ ones (n+2) := by
  have hex : ∃ x, x ∈ D ∧ dot (pairWord n) x ≠ 0 := by
    by_contra hn
    apply hp
    apply (hD _).mpr
    intro x hx
    by_contra hd
    exact hn ⟨x, hx, hd⟩
  obtain ⟨x, hx, hd⟩ := hex
  refine ⟨x, hx, ?_, ?_⟩
  · intro h
    apply hd
    rw [h, dot_pairWord]
    rfl
  · intro h
    apply hd
    rw [h, dot_pairWord]
    exact add_self_zero 1

/-- A weight-two word can be sent to the first adjacent pair by one
coordinate permutation. -/
theorem exists_weightTwo_permutation (x : BinaryVector (n+2)) (hx : binaryWeight x = 2) :
    ∃ e : Fin (n+2) ≃ Fin (n+2), coordinateMap e (pairWord n) = x := by
  obtain ⟨a, b, hab, hs⟩ := Finset.card_eq_two.mp (show (wordSupport x).card = 2 from hx)
  let f : Fin (n+2) ≃ Fin (n+2) := Equiv.swap a 0
  have hfa : f a = 0 := Equiv.swap_apply_left a 0
  have hfb : f b ≠ 0 := by
    intro h
    have H : b = a := f.injective (h.trans hfa.symm)
    exact hab H.symm
  have h01 : (0 : Fin (n+2)) ≠ 1 := by intro h; have H := congrArg Fin.val h; simp at H
  let e := f.trans (Equiv.swap (f b) 1)
  have hea : e a = 0 := by
    change Equiv.swap (f b) 1 (f a) = 0
    rw [hfa, Equiv.swap_apply_of_ne_of_ne (Ne.symm hfb) h01]
  have heb : e b = 1 := Equiv.swap_apply_left (f b) 1
  have he0 (i : Fin (n+2)) : e i = 0 ↔ i = a := by rw [← hea]; exact e.apply_eq_iff_eq
  have he1 (i : Fin (n+2)) : e i = 1 ↔ i = b := by rw [← heb]; exact e.apply_eq_iff_eq
  have hp : pairWord n = supportWord {0, 1} := by
    funext i
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i
    · simp [pairWord, prepend, supportWord]
    · simp [pairWord, prepend, supportWord]
    · have hne1 : k.succ.succ ≠ (1 : Fin (n+2)) := by
        intro h
        have H := congrArg Fin.val h
        simp only [Fin.val_succ, Fin.val_one] at H
        omega
      simp [pairWord, prepend, supportWord, Fin.succ_ne_zero, hne1]
  refine ⟨e, ?_⟩
  rw [hp, ← supportWord_wordSupport x, hs]
  funext i
  change (if e i ∈ ({0, 1} : Finset (Fin (n+2))) then (1:ZMod 2) else 0) =
    if i ∈ ({a, b} : Finset (Fin (n+2))) then 1 else 0
  simp [he0, he1]

/-- One stage of elimination finds the first repetition pair using at most
`n+2` actual gates, while keeping the whole transformed code self-dual. -/
theorem exists_pair_reduction (D : BinaryCode (n+2)) (hD : SelfDual D) :
    ∃ p : GenerationProgram (n+2), p.length ≤ n+2 ∧ pairWord n ∈ p.run D := by
  by_cases hp : pairWord n ∈ D
  · exact ⟨[], by simp, hp⟩
  obtain ⟨x, hx, h0, h1⟩ := exists_proper_word_of_pair_missing D hD hp
  obtain ⟨p, z, hlen, hz, hwt⟩ := exists_weightTwo_reduction D hD x hx h0 h1
  obtain ⟨e, he⟩ := exists_weightTwo_permutation z hwt
  refine ⟨GenerationGate.perm e :: p, ?_, ?_⟩
  · have hb := binaryWeight_le x
    simp only [List.length_cons]
    omega
  · change coordinateMap e (pairWord n) ∈ p.run D
    rwa [he]

end
end Holant.ReedMuller.FlatNetwork
