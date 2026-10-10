import Holant.Proofs.Hardness.GeneralEOCentralHolePatternsTerminal
import Holant.Proofs.Hardness.GeneralEOCentralHoleRepeated

/-! Coordinate normalization for actual central-hole network reductions.
The equivalence acts only on the boundary of the given graph. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOCentralHoleCoordinates
open Holant Holant.Tractable
set_option backward.isDefEq.respectTransparency false
namespace P
export GeneralEOCentralHolePatterns (ConstantColumns RepeatedColumns10 alternating)
end P
namespace N
export GeneralEOPinnedDescentNetwork (reboundary reboundary_denote reboundaryLabels)
end N
namespace O
export GeneralEOPinnedDescentOperations (word pinned)
end O
namespace S
export GeneralEOCentralHoleStep (word_xor pin_hole pinned_central)
end S
namespace R
export GeneralEOCentralHoleRepeated (double output output_hole output_central)
end R
namespace H
export GeneralEONegativeSupportTensor (CentralHole)
end H
variable {K : Type*} [Field K] {n m : ℕ}

theorem weight_comp (a : Fin n → Bool) (e : Fin m ≃ Fin n) :
    weight (a ∘ e) = weight a :=
  Fintype.sum_equiv e _ _ (fun _ => rfl)

theorem charge_comp (a : Fin n → Bool) (e : Fin m ≃ Fin n) :
    charge (a ∘ e) = charge a := by
  have hn : m = n := by simpa only [Fintype.card_fin] using Fintype.card_congr e
  simp only [charge, weight_comp, hn]

theorem xor_comp (a b c : Fin n → Bool) (e : Fin m ≃ Fin n) :
    tripleXor (a ∘ e) (b ∘ e) (c ∘ e) = (tripleXor a b c) ∘ e := rfl

theorem reboundary_word (T : Network K n) (e : Fin m ≃ Fin n)
    (a : Fin n → Bool) : (N.reboundary T e.symm).denote (a ∘ e) = T.denote a := by
  rw [N.reboundary_denote, Tensor.reindex_apply]
  congr 1
  funext i
  simp only [Function.comp_apply, Equiv.apply_symm_apply]

theorem reboundary_central (T : Network K n) (e : Fin m ≃ Fin n)
    (he : Signature.CentralSupport T.denote) :
    Signature.CentralSupport (N.reboundary T e.symm).denote := by
  intro x hx
  rw [N.reboundary_denote, Tensor.reindex_apply]
  apply he
  have hn : n = m := by simpa only [Fintype.card_fin] using Fintype.card_congr e.symm
  change 2 * weight (x ∘ e.symm) ≠ n
  rw [weight_comp,hn]
  exact hx

/-- Boundary equivalence preserves the actual missing balanced triple xor. -/
theorem reboundary_hole (T : Network K n) (e : Fin m ≃ Fin n)
    (hh : H.CentralHole T.denote) : H.CentralHole (N.reboundary T e.symm).denote := by
  obtain ⟨t,hz,hd⟩ := hh
  refine ⟨⟨t.first ∘ e,t.second ∘ e,t.third ∘ e,?_,?_,?_⟩,?_,?_⟩
  · simpa only [reboundary_word] using t.first_supported
  · simpa only [reboundary_word] using t.second_supported
  · simpa only [reboundary_word] using t.third_supported
  · change (N.reboundary T e.symm).denote
      (tripleXor (t.first ∘ e) (t.second ∘ e) (t.third ∘ e)) = 0
    rw [xor_comp,reboundary_word]
    exact hz
  · change charge (tripleXor (t.first ∘ e) (t.second ∘ e) (t.third ∘ e)) = 0
    rw [xor_comp,charge_comp]
    exact hd

def tail2 (a : Fin (n+2) → Bool) : Fin n → Bool := fun i => a i.succ.succ

theorem word_tail (a : Fin (n+2) → Bool) :
    O.word (a 0) (a 1) (tail2 a) = a := by
  funext i
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun _ => ?_) i) i <;> rfl

theorem prefix_two (a : Fin (n+2) → Bool) (u v : Bool)
    (h : 2 ≤ n+2) (hp : a ∘ Fin.castLE h = ![u,v]) :
    a = O.word u v (tail2 a) := by
  have h0 : a 0 = u := by simpa using congrFun hp 0
  have h1 : a 1 = v := by
    have hi : Fin.castLE h (1 : Fin 2) = (1 : Fin (n+2)) := by
      apply Fin.ext
      simp (disch := omega) [Nat.mod_eq_of_lt]
    simpa [hi] using congrFun hp 1
  rw [←h0, ←h1, word_tail]

def tail4 (a : Fin (n+4) → Bool) : Fin n → Bool := tail2 (tail2 a)

theorem prefix_four (a : Fin (n+4) → Bool) (u : Bool)
    (h : 4 ≤ n+4) (hp : a ∘ Fin.castLE h = P.alternating u) :
    a = R.double u u (tail4 a) := by
  have h0 : a 0 = u := by simpa [P.alternating] using congrFun hp 0
  have h1 : a 1 = !u := by
    have hi : Fin.castLE h (1 : Fin 4) = (1 : Fin (n+4)) := by
      apply Fin.ext
      simp (disch := omega) [Nat.mod_eq_of_lt]
    simpa [P.alternating,hi] using congrFun hp 1
  have h2 : a 2 = u := by
    have hi : Fin.castLE h (2 : Fin 4) = (2 : Fin (n+4)) := by
      apply Fin.ext
      simp (disch := omega) [Nat.mod_eq_of_lt]
    simpa [P.alternating,hi] using congrFun hp 2
  have h3 : a 3 = !u := by
    have hi : Fin.castLE h (3 : Fin 4) = (3 : Fin (n+4)) := by
      apply Fin.ext
      simp (disch := omega) [Nat.mod_eq_of_lt]
    simpa [P.alternating,hi] using congrFun hp 3
  funext i
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => Fin.cases ?_
    (fun i => Fin.cases ?_ (fun _ => ?_) i) i) i) i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · rfl

theorem xor_swap_last (a b c : Fin n → Bool) : tripleXor a c b = tripleXor a b c := by
  funext i
  dsimp [tripleXor]
  cases a i <;> cases b i <;> cases c i <;> rfl

theorem xor_cycle (a b c : Fin n → Bool) : tripleXor b c a = tripleXor a b c := by
  funext i
  dsimp [tripleXor]
  cases a i <;> cases b i <;> cases c i <;> rfl

/-- Every constant-column prefix is literally a directed paired-pin input. -/
theorem constant_hole (T : Network K (n+2)) (a b c : Fin (n+2) → Bool)
    (ha : T.denote a ≠ 0) (hb : T.denote b ≠ 0) (hc : T.denote c ≠ 0)
    (hz : T.denote (tripleXor a b c) = 0) (hd : charge (tripleXor a b c) = 0)
    (h : 2 ≤ n+2) (e : Equiv.Perm (Fin (n+2)))
    (hp : P.ConstantColumns a b c (fun i => e (Fin.castLE h i))) :
    H.CentralHole (O.pinned (N.reboundary T e.symm) false).denote := by
  obtain ⟨pa,pb,pc⟩ := hp
  have ea := prefix_two (a ∘ e) false true h pa
  have eb := prefix_two (b ∘ e) false true h pb
  have ec := prefix_two (c ∘ e) false true h pc
  have hx : (tripleXor a b c) ∘ e =
      O.word false true (tripleXor (tail2 (a ∘ e)) (tail2 (b ∘ e)) (tail2 (c ∘ e))) := by
    rw [←xor_comp,ea,eb,ec,S.word_xor]
    rfl
  apply S.pin_hole (N.reboundary T e.symm) false
    (tail2 (a ∘ e)) (tail2 (b ∘ e)) (tail2 (c ∘ e))
  · simpa only [Bool.not_false, ←ea, reboundary_word] using ha
  · simpa only [Bool.not_false, ←eb, reboundary_word] using hb
  · simpa only [Bool.not_false, ←ec, reboundary_word] using hc
  · simpa only [Bool.not_false, ←hx, reboundary_word] using hz
  · simpa only [Bool.not_false, ←hx, charge_comp] using hd

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOCentralHoleCoordinates
