import Holant.Proofs.Reductions.GeneralExtraction.SupportCaps
import Holant.NetworkGluing
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring


noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.Hardness.GeneralExtraction.BinaryCarrier
open NamedContraction SupportDescent SupportCaps
open Holant.LocalDrafts.BinaryInterpolation.SingularExtraction

variable {K : Type*} [Field K] {n : ℕ}

def words : (Fin 2 → Bool) ≃ Bool × Bool where
  toFun x := (x 0, x 1)
  invFun p := ![p.1, p.2]
  left_inv x := by funext i; fin_cases i <;> rfl
  right_inv _ := rfl

def swapped (N : Network K 2) : Network K 2 :=
  reboundary N (Equiv.swap 0 1)

def parallel (N : Network K 2) : Network K 0 := N.glue N (fun _ => Signature.disequality)
def crossed (N : Network K 2) : Network K 0 := N.glue (swapped N) (fun _ => Signature.disequality)

theorem parallel_value (N : Network K 2) :
    (parallel N).denote Fin.elim0 =
      2 * N.denote ![false, false] * N.denote ![true, true] +
      2 * N.denote ![false, true] * N.denote ![true, false] := by
  rw [parallel, Network.denote_glue]
  rw [← words.symm.sum_comp]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  simp_rw [← words.symm.sum_comp]
  simp [words, Equiv.coe_fn_symm_mk, Fintype.sum_prod_type, Fintype.sum_bool, Fin.prod_univ_succ,
    Signature.disequality]
  ring

theorem crossed_value (N : Network K 2) :
    (crossed N).denote Fin.elim0 =
      2 * N.denote ![false, false] * N.denote ![true, true] +
      N.denote ![false, true] ^ 2 + N.denote ![true, false] ^ 2 := by
  rw [crossed, Network.denote_glue]
  rw [← words.symm.sum_comp]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  simp_rw [← words.symm.sum_comp]
  have hs : ∀ a b : Bool, (fun i : Fin 2 => ![a,b] (Equiv.swap 0 1 i)) = ![b,a] := by
    intro a b
    funext i
    fin_cases i <;> simp [Equiv.swap_apply_def]
  simp [words, Equiv.coe_fn_symm_mk, swapped, reboundary_denote, Fintype.sum_prod_type, Fintype.sum_bool,
    Fin.prod_univ_succ, Signature.disequality, hs]
  ring

theorem glue_uses (F : SignatureFamily K) (L R : Network K n)
    (hL : Uses L F) (hR : Uses R F) :
    Uses (L.glue R (fun _ => Signature.disequality)) F := by
  intro v
  change (⟨_, (Network.glueFinite L R (fun _ => Signature.disequality)).vertex
    ((Fintype.equivFin (Fin L.shape.vertices ⊕ Fin R.shape.vertices)).symm v)⟩ : AnySignature K) ∈ F
  cases (Fintype.equivFin (Fin L.shape.vertices ⊕ Fin R.shape.vertices)).symm v with
  | inl v => exact hL v
  | inr v => exact hR v

theorem glue_native (L R : Network K n) (hL : Native L) (hR : Native R) :
    Native (L.glue R (fun _ => Signature.disequality)) := by
  intro e
  change (Network.glueFinite L R (fun _ => Signature.disequality)).edge
    ((Fintype.equivFin (Network.GluedEdges L R)).symm e) = _
  rcases (Fintype.equivFin (Network.GluedEdges L R)).symm e with (l | r) | i
  · exact hL l
  · exact hR r
  · rfl

theorem close_nonzero (F : SignatureFamily K) (htwo : (2 : K) ≠ 0)
    (N : Network K 2) (hU : Uses N F) (hN : Native N)
    (hentry : N.denote ![false, true] ≠ 0 ∨ N.denote ![true, false] ≠ 0) :
    ∃ C : Network K 0, Uses C F ∧ Native C ∧
      0 < C.shape.vertices ∧ C.denote Fin.elim0 ≠ 0 := by
  have hNv : 0 < N.shape.vertices := by
    by_contra hn
    have hv : N.shape.vertices = 0 := Nat.eq_zero_of_not_pos hn
    have hports := Fintype.card_congr N.shape.ports
    simp [hv] at hports
    omega
  by_cases hcap : (N.contract Signature.disequality).denote Fin.elim0 ≠ 0
  · refine ⟨N.contract Signature.disequality, hU, ?_, hNv, hcap⟩
    intro e
    refine Fin.cases rfl (fun e => hN e) e
  have hbc : N.denote ![false, true] + N.denote ![true, false] = 0 := by
    have h := not_ne_iff.mp hcap
    rw [Network.denote_contract_disequality] at h
    exact h
  have hb : N.denote ![false, true] ≠ 0 := by
    rcases hentry with h | h
    · exact h
    · intro hz
      apply h
      simpa [hz] using hbc
  have hc : N.denote ![true, false] = -N.denote ![false, true] := by
    exact eq_neg_of_add_eq_zero_right hbc
  by_cases hp : (parallel N).denote Fin.elim0 ≠ 0
  · exact ⟨parallel N, glue_uses F N N hU hU, glue_native N N hN hN,
      by simpa [parallel] using Nat.add_pos_left hNv N.shape.vertices, hp⟩
  have hq : (crossed N).denote Fin.elim0 ≠ 0 := by
    intro hq
    have ep := parallel_value N
    have eq := crossed_value N
    rw [hc] at ep eq
    have hp0 := not_ne_iff.mp hp
    have hz : ((2 : K) * 2) * (N.denote ![false, true]) ^ 2 = 0 := by
      linear_combination ep - eq - hp0 + hq
    exact (mul_ne_zero (mul_ne_zero htwo htwo) (pow_ne_zero 2 hb)) hz
  exact ⟨crossed N, glue_uses F N (swapped N) hU hU,
    glue_native N (swapped N) hN hN,
    by simpa [crossed, swapped, reboundary] using Nat.add_pos_left hNv N.shape.vertices, hq⟩

/-- A supported balanced word of ANY positive arity yields a nonzero
closed ordinary graph over the same original labels. -/
theorem balanced_carrier (F : SignatureFamily K) (htwo : (2 : K) ≠ 0)
    {n : ℕ} (hn : 0 < n) (N : Network K n) (hU : Uses N F) (hN : Native N)
    (x : Fin n → Bool) (hx : N.denote x ≠ 0) (hb : balance true x = 0) :
    ∃ C : Network K 0, Uses C F ∧ Native C ∧
      0 < C.shape.vertices ∧ C.denote Fin.elim0 ≠ 0 := by
  have hl : ∀ z, N.denote z ≠ 0 → -(n : ℤ) ≤ balance true z := by
    intro z _
    rw [balance_count]
    simp only [Fintype.card_fin]
    omega
  obtain ⟨m, M, y, hMU, hMN, hMv, hMy, hMb, _, hstop, hpos⟩ :=
    terminal F htwo true (-(n : ℤ)) n N hU hN x hx (by omega) hl
  have hmpos := hpos hn
  have hmy : balance true y = 0 := hMb.trans hb
  have hmle : m ≤ 2 := by
    rcases hstop with hall | hm
    · have he : balance true y = (m : ℤ) := by simp [balance, hall]
      omega
    · exact hm
  have hm : m = 2 := by
    have hcount := balance_count true y
    simp only [Fintype.card_fin] at hcount
    omega
  subst m
  apply close_nonzero F htwo M hMU hMN
  have hy : y 0 ≠ y 1 := by
    intro he
    cases h0 : y 0 <;> cases h1 : y 1 <;>
      simp_all [balance, Fin.sum_univ_succ]
  have he : y = ![y 0, y 1] := by funext i; fin_cases i <;> rfl
  cases h0 : y 0 <;> cases h1 : y 1
  · exact False.elim (hy (h0.trans h1.symm))
  · exact Or.inl (by rw [he, h0, h1] at hMy; exact hMy)
  · exact Or.inr (by rw [he, h0, h1] at hMy; exact hMy)
  · exact False.elim (hy (h0.trans h1.symm))

end Holant.LocalDrafts.Hardness.GeneralExtraction.BinaryCarrier
