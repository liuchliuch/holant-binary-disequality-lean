import Holant.Proofs.Hardness.GeneralEOCentralHolePatterns

/-! Actual prefix permutations for the complementary-column cases. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOCentralHolePatterns
open Holant Holant.Tractable
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} (a b c : Fin n → Bool)

/-- The prefix used by the literal directed paired pin. -/
def ConstantColumns (v : Fin 2 → Fin n) : Prop :=
  a ∘ v = ![false,true] ∧ b ∘ v = ![false,true] ∧ c ∘ v = ![false,true]

/-- The prefix used by the repeated-class descent: two common 10 pairs and
one exceptional 01 pair, with all three possible exceptional rows explicit. -/
def RepeatedColumns10 (v : Fin 4 → Fin n) : Prop :=
  (a ∘ v = alternating true ∧ b ∘ v = alternating true ∧ c ∘ v = alternating false) ∨
  (a ∘ v = alternating true ∧ c ∘ v = alternating true ∧ b ∘ v = alternating false) ∨
  (b ∘ v = alternating true ∧ c ∘ v = alternating true ∧ a ∘ v = alternating false)

theorem repeatedColumns_reverse (v : Fin 4 → Fin n) (hv : RepeatedColumns a b c v) :
    RepeatedColumns10 a b c (v ∘ reverseFour) := by
  have hr (w : Fin n → Bool) (t : Bool) (hw : w ∘ v = alternating t) :
      w ∘ (v ∘ reverseFour) = alternating (!t) := by
    rw [←Function.comp_assoc,hw,alternating_reverse]
  rcases hv with h | h | h
  · exact Or.inl ⟨hr a false h.1,hr b false h.2.1,hr c true h.2.2⟩
  · exact Or.inr (Or.inl ⟨hr a false h.1,hr c false h.2.1,hr b true h.2.2⟩)
  · exact Or.inr (Or.inr ⟨hr b false h.1,hr c false h.2.1,hr a true h.2.2⟩)

theorem constant_prefix_permutation (i j : Fin n) (hij : i ≠ j)
    (hai : a i = false) (hbi : b i = false) (hci : c i = false)
    (haj : a j = true) (hbj : b j = true) (hcj : c j = true) :
    ∃ (h : 2 ≤ n) (e : Equiv.Perm (Fin n)),
      ConstantColumns a b c (fun t => e (Fin.castLE h t)) := by
  let v : Fin 2 → Fin n := ![i,j]
  have hv : Function.Injective v := by
    intro s t h
    fin_cases s <;> fin_cases t <;> simp_all [v]
  obtain ⟨h,e,he⟩ := exists_prefix_permutation v hv
  have he' : (fun t => e (Fin.castLE h t)) = v := funext he
  refine ⟨h,e,?_⟩
  rw [he']
  refine ⟨?_,?_,?_⟩
  all_goals
    funext t
    fin_cases t <;> simp [v,hai,hbi,hci,haj,hbj,hcj]

theorem repeated_prefix_permutation (v : Fin 4 → Fin n) (hi : Function.Injective v)
    (hv : RepeatedColumns a b c v) :
    ∃ (h : 4 ≤ n) (e : Equiv.Perm (Fin n)),
      RepeatedColumns10 a b c (fun t => e (Fin.castLE h t)) := by
  obtain ⟨h,e,he⟩ := exists_prefix_permutation (v ∘ reverseFour) (hi.comp reverseFour.injective)
  have he' : (fun t => e (Fin.castLE h t)) = v ∘ reverseFour := funext he
  refine ⟨h,e,?_⟩
  rw [he']
  exact repeatedColumns_reverse a b c v hv

/-- Prefix permutations act on the original coordinates of the input signature;
the pairing is only an internal proof of the alternatives. -/
theorem central_prefix_partition (f : Signature AlgebraicComplex n)
    (he : Signature.CentralSupport f) (ha : f a ≠ 0) (hb : f b ≠ 0) (hc : f c ≠ 0)
    (hd : charge (tripleXor a b c) = 0) :
    (∃ (h : 2 ≤ n) (e : Equiv.Perm (Fin n)),
      ConstantColumns a b c (fun t => e (Fin.castLE h t))) ∨
    (∃ (h : 4 ≤ n) (e : Equiv.Perm (Fin n)),
      RepeatedColumns10 a b c (fun t => e (Fin.castLE h t))) ∨ n ≤ 6 := by
  rcases central_coordinate_partition a b c f he ha hb hc hd with h | h | h
  · obtain ⟨i,j,hij,hai,hbi,hci,haj,hbj,hcj⟩ := h
    exact Or.inl (constant_prefix_permutation a b c i j hij hai hbi hci haj hbj hcj)
  · obtain ⟨v,hi,hv⟩ := h
    exact Or.inr (Or.inl (repeated_prefix_permutation a b c v hi hv))
  · exact Or.inr (Or.inr h)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOCentralHolePatterns
