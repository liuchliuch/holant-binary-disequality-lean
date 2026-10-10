import Holant.Proofs.Reductions.GeneralExtraction.SupportDescent
import Mathlib.Data.Set.Finite.Lemmas


noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.Hardness.GeneralExtraction.SupportCaps
open NamedContraction SupportDescent
open Holant.LocalDrafts.BinaryInterpolation.SingularExtraction
open Holant.Certificates.MatchingContractionClosure

variable {K : Type*} [Field K]

/-- A graph-level induction that stops at a monochromatic word or arity ≤2.
The lower support bound is carried through all branches, including the
swapped-word branch of the triangle argument. -/
theorem terminal (F : SignatureFamily K) (htwo : (2 : K) ≠ 0) (b : Bool)
    (lower : ℤ) (n : ℕ) (N : Network K n) (hU : Uses N F) (hN : Native N)
    (x : Fin n → Bool) (hx : N.denote x ≠ 0) (hb : 0 ≤ balance b x)
    (hbound : ∀ z, N.denote z ≠ 0 → lower ≤ balance b z) :
    ∃ m : ℕ, ∃ M : Network K m, ∃ y : Fin m → Bool,
      Uses M F ∧ Native M ∧ M.shape.vertices = N.shape.vertices ∧
      M.denote y ≠ 0 ∧ balance b y = balance b x ∧
      (∀ z, M.denote z ≠ 0 → lower ≤ balance b z) ∧
      ((∀ i, y i = b) ∨ m ≤ 2) ∧ (0 < n → 0 < m) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hall : ∀ i, x i = b
    · exact ⟨n, N, x, hU, hN, rfl, hx, rfl, hbound, Or.inl hall, fun h => h⟩
    by_cases hn : n ≤ 2
    · exact ⟨n, N, x, hU, hN, rfl, hx, rfl, hbound, Or.inr hn, fun h => h⟩
    push_neg at hall
    obtain ⟨i, j, hij, y, hy, hby⟩ := exact_contraction htwo b N.denote x hx hb
      (by simpa using Nat.lt_of_not_ge hn) hall
    let C := (ofNetwork N).close i j hij
    let e := C.boundary
    let y' : Fin C.arity → Bool := fun a => y (e.symm a)
    have hcy : C.graph.denote y' ≠ 0 := by
      change C.denote y ≠ 0
      rw [Named.close_denote]
      exact hy
    have hbal : balance b y' = balance b x :=
      (balance_reindex e.symm b y).trans hby
    have hcb : ∀ z, C.graph.denote z ≠ 0 → lower ≤ balance b z := by
      intro z hz
      have hz' : C.denote (fun a => z (e a)) ≠ 0 := by
        simpa [Named.denote, e] using hz
      rw [Named.close_denote] at hz'
      obtain ⟨w, hw, hbw⟩ := contraction_support b N.denote i j hij _ hz'
      have H := hbound w hw
      rwa [hbw, balance_reindex e b z] at H
    have hc := remaining_card i j hij
    simp only [Fintype.card_fin] at hc
    have hlt : C.arity < n := by dsimp [C, Named.close]; simpa using (by omega : Fintype.card (Remaining i j) < n)
    have hCpos : 0 < C.arity := by dsimp [C, Named.close]; omega
    obtain ⟨m, M, z, hMU, hMN, hMv, hMz, hMb, hML, hstop, hmpos⟩ :=
      ih C.arity hlt C.graph
        ((ofNetwork N).close_uses i j hij F hU)
        ((ofNetwork N).close_native i j hij hN) y' hcy (by rw [hbal]; exact hb) hcb
    exact ⟨m, M, z, hMU, hMN, hMv, hMz, hMb.trans hbal, hML, hstop, fun _ => hmpos hCpos⟩

/-- Exact positive charge determines the final arity. Original vertices are
unchanged; when starting at a corolla this is a ONE-copy self-loop gadget. -/
theorem positive_cap (F : SignatureFamily K) (htwo : (2 : K) ≠ 0) (b : Bool)
    (lower : ℤ) {n : ℕ} (N : Network K n) (hU : Uses N F) (hN : Native N)
    (x : Fin n → Bool) (hx : N.denote x ≠ 0) (hb : 0 < balance b x)
    (hbound : ∀ z, N.denote z ≠ 0 → lower ≤ balance b z) :
    ∃ m : ℕ, 0 < m ∧ ∃ M : Network K m,
      Uses M F ∧ Native M ∧ M.shape.vertices = N.shape.vertices ∧
      (m : ℤ) = balance b x ∧ M.denote (fun _ => b) ≠ 0 ∧
      (∀ z, M.denote z ≠ 0 → lower ≤ balance b z) := by
  obtain ⟨m, M, y, hMU, hMN, hMv, hMy, hMb, hML, hstop, _⟩ :=
    terminal F htwo b lower n N hU hN x hx (le_of_lt hb) hbound
  have hall : y = fun _ => b := by
    rcases hstop with hall | hm
    · exact funext hall
    · apply all_eq_of_card_le_balance b y
      have hcount := balance_count b y
      have hle := matches_le b y
      simp only [Fintype.card_fin] at *
      omega
  have he : (m : ℤ) = balance b x := by
    simpa [hall, balance] using hMb
  exact ⟨m, by omega, M, hMU, hMN, hMv, he, hall ▸ hMy, hML⟩

def purePin (c : K) (b : Bool) (n : ℕ) : Signature K n :=
  fun x => if x = (fun _ => b) then c else 0

/-- Strict one-sided support produces a genuine nonzero pure pin, by
minimizing the ORIGINAL support balance before the loop descent. -/
theorem strict_side_pin (htwo : (2 : K) ≠ 0) (b : Bool) {n : ℕ}
    (f : Signature K n) (hf : f ≠ 0)
    (hside : ∀ x, f x ≠ 0 → 0 < balance b x) :
    ∃ m : ℕ, 0 < m ∧ ∃ c : K, c ≠ 0 ∧ ∃ M : Network K m,
      Uses M {⟨n, f⟩} ∧ Native M ∧ M.shape.vertices = 1 ∧ M.denote = purePin c b m := by
  have hnonempty : {x | f x ≠ 0}.Nonempty := by
    obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
      by_contra hn
      push_neg at hn
      exact hf (funext hn)
    exact ⟨x, hx⟩
  obtain ⟨x, hx, hmin⟩ := Set.exists_min_image {x | f x ≠ 0}
    (balance b) (Set.toFinite _) hnonempty
  obtain ⟨m, hm, M, hU, hN, hV, hcharge, hvalue, hbound⟩ :=
    positive_cap {⟨n, f⟩} htwo b (balance b x) (Network.corolla f)
      (fun _ => Set.mem_singleton _) (fun e => Fin.elim0 e) x
      (by simpa using hx) (hside x hx) (by simpa using hmin)
  refine ⟨m, hm, M.denote (fun _ => b), hvalue, M, hU, hN, hV, ?_⟩
  funext z
  by_cases hz : z = fun _ => b
  · simp [purePin, hz]
  · have hv : M.denote z = 0 := by
      by_contra hv
      apply hz
      apply all_eq_of_card_le_balance b z
      simpa only [Fintype.card_fin, hcharge] using hbound z hv
    simp [purePin, hz, hv]

/-- Lemma 40 itself, with a singleton original label and one original vertex. -/
theorem support_cap (htwo : (2 : K) ≠ 0) (b : Bool) {n : ℕ}
    (f : Signature K n) (x : Fin n → Bool) (hx : f x ≠ 0) (hb : 0 < balance b x) :
    ∃ m : ℕ, 0 < m ∧ ∃ M : Network K m,
      Uses M {⟨n, f⟩} ∧ Native M ∧ M.shape.vertices = 1 ∧
      (m : ℤ) = balance b x ∧ M.denote (fun _ => b) ≠ 0 := by
  have hl : ∀ z, (Network.corolla f).denote z ≠ 0 → -(n : ℤ) ≤ balance b z := by
    intro z _
    rw [balance_count]
    simp only [Fintype.card_fin]
    omega
  obtain ⟨m, hm, M, hU, hN, hV, hc, hv, _⟩ :=
    positive_cap {⟨n, f⟩} htwo b (-(n : ℤ)) (Network.corolla f)
      (fun _ => Set.mem_singleton _) (fun e => Fin.elim0 e) x
      (by simpa using hx) hb hl
  exact ⟨m, hm, M, hU, hN, hV, hc, hv⟩

end Holant.LocalDrafts.Hardness.GeneralExtraction.SupportCaps
