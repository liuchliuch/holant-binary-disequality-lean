import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXLocalStarCriterion

/-! The coordinate bookkeeping for a fixed equality pair. A triple using
at least two pair endpoints has an outside nonendpoint in dimension four. -/
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralSinglePairCount
open Holant
variable {n : ℕ} (p q : Fin n)
def hit (i : Fin n) : ℕ := if i=p ∨ i=q then 1 else 0
def count (i j k : Fin n) : ℕ := hit p q i+hit p q j+hit p q k

theorem hit_le (i : Fin n) : hit p q i≤1 := by unfold hit;split <;> omega

theorem swap_first (i j k : Fin n) : count p q i j k=count p q j i k := by simp [count,Nat.add_comm]
theorem swap_last (i j k : Fin n) : count p q i j k=count p q i k j := by simp only [count];omega

theorem triple_card (a b c : Fin n) : ({a,b,c} : Finset (Fin n)).card≤3 := by
  exact (Finset.card_insert_le _ _).trans (by
    have h:=Finset.card_insert_le b ({c} : Finset (Fin n))
    simpa using Nat.add_le_add_right h 1)

theorem outside (higher : 4≤n) (i j k : Fin n) (ip : i=p ∨ i=q) (large : 2≤count p q i j k) :
    ∃r : Fin n,r≠p ∧ r≠q ∧ r≠i ∧ r≠j ∧ r≠k := by
  classical
  have others : j=p ∨ j=q ∨ k=p ∨ k=q := by
    by_contra h
    push Not at h
    simp only [count,hit,ite_eq_left ip,ite_eq_right (not_or.mpr ⟨h.1,h.2.1⟩),
      ite_eq_right (not_or.mpr ⟨h.2.2.1,h.2.2.2⟩)] at large
    omega
  let S : Finset (Fin n):={p,q,j,k}
  have small : S.card≤3 := by
    rcases others with h|h|h|h
    · apply (Finset.card_le_card (s:=S) (t:={p,q,k}) ?_).trans (triple_card p q k)
      intro x hx;simp only [S,Finset.mem_insert,Finset.mem_singleton,h] at hx ⊢;tauto
    · apply (Finset.card_le_card (s:=S) (t:={p,q,k}) ?_).trans (triple_card p q k)
      intro x hx;simp only [S,Finset.mem_insert,Finset.mem_singleton,h] at hx ⊢;tauto
    · apply (Finset.card_le_card (s:=S) (t:={p,q,j}) ?_).trans (triple_card p q j)
      intro x hx;simp only [S,Finset.mem_insert,Finset.mem_singleton,h] at hx ⊢;tauto
    · apply (Finset.card_le_card (s:=S) (t:={p,q,j}) ?_).trans (triple_card p q j)
      intro x hx;simp only [S,Finset.mem_insert,Finset.mem_singleton,h] at hx ⊢;tauto
  have positive : 0<Sᶜ.card := by
    rw [Finset.card_compl]
    simp only [Fintype.card_fin]
    omega
  obtain ⟨r,hr⟩:=Finset.card_pos.mp positive
  have notmem:=Finset.mem_compl.mp hr
  have rp : r≠p := by intro h;exact notmem (by simp [S,h])
  have rq : r≠q := by intro h;exact notmem (by simp [S,h])
  refine ⟨r,rp,rq,?_,?_,?_⟩
  · rcases ip with rfl|rfl <;> assumption
  · intro h;exact notmem (by simp [S,h])
  · intro h;exact notmem (by simp [S,h])

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralSinglePairCount
