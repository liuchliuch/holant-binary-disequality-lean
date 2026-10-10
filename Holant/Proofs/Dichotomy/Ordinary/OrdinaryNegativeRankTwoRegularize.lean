import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeRankTwoPorts
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeSignedRowsSource

/-! Actual rank-two parity regularization from arbitrary signed bundle
multiplicities. If the three bundles are not all odd, at most three pinned
original rows turn every essential incidence even. Constants and unsquared
coefficients are retained exactly; no oracle backend is a hypothesis. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeRankTwoRegularize
open Holant Holant.Tractable
open OrdinaryNegativeSignedPortsCore OrdinaryNegativeRankTwoPorts
open scoped BigOperators
namespace I
export OrdinaryNegativeSignedPortsIncidence (bundleSize)
end I
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
variable {n : ℕ} (p : Fin n→Port 3)

def basePort (i : Fin n) : Port 3 :=
  match p i with
  | .inl b=>.inl b
  | .inr (_,s)=>.inl s

theorem base_word (z : Fin 3→Bool) : word (basePort p) z=word p (fun _=>false) := by
  funext i
  cases h : p i with
  | inl b=>simp [basePort,word,h]
  | inr t=>rcases t with ⟨j,s⟩;simp [basePort,word,h]

theorem base_count (j : Fin 3) : I.bundleSize (basePort p) j=0 := by
  unfold I.bundleSize
  apply Finset.sum_eq_zero
  intro i _
  cases h : p i with
  | inl b=>simp [basePort,h]
  | inr t=>rcases t with ⟨j,s⟩;simp [basePort,h]

def correction (axis : Fin 2) (j : Fin 3) : Fin n→Port 3 :=
  if Odd (I.bundleSize p j) then linePort p axis j else basePort p

def rows (axis : Fin 2) : Fin 4→Fin n→Port 3 :=
  Fin.cases p (correction p axis)

theorem correction_count (axis : Fin 2) (j k : Fin 3) :
    I.bundleSize (correction p axis j) k=
      if j=k ∧ Odd (I.bundleSize p j) then lineSize p axis else 0 := by
  by_cases h : Odd (I.bundleSize p j)
  · simp only [correction,h,ite_true,line_count]
    by_cases hj : j=k <;> simp [hj,h]
  · simp [correction,h,base_count]

theorem rows_count (axis : Fin 2) (k : Fin 3) :
    (∑i : Fin 4,I.bundleSize (rows p axis i) k)=
      I.bundleSize p k+(if Odd (I.bundleSize p k) then lineSize p axis else 0) := by
  rw [Fin.sum_univ_succ]
  simp only [rows,Fin.cases_zero,Fin.cases_succ,correction_count]
  congr 1
  rw [Finset.sum_eq_single k]
  · simp
  · intro j _ hj
    simp [hj]
  · simp

theorem even_rows (axis : Fin 2) (h : Odd (lineSize p axis)) :
    ∀k,Even (∑i : Fin 4,I.bundleSize (rows p axis i) k) := by
  intro k
  rw [rows_count]
  by_cases hk : Odd (I.bundleSize p k)
  · rw [if_pos hk]
    rcases hk with ⟨a,ha⟩
    rcases h with ⟨b,hb⟩
    refine ⟨a+b+1,?_⟩
    omega
  · rw [if_neg hk,Nat.add_zero]
    exact (Nat.even_or_odd _).resolve_right hk

/-- The direction is chosen from the two actual information coordinates.
An absent dependent bundle causes no diagonal pinning obligation. -/
theorem even_or_all_odd_or_line :
    (∀j,Even (I.bundleSize p j)) ∨ (∀j,Odd (I.bundleSize p j)) ∨
      ∃axis : Fin 2,Odd (lineSize p axis) := by
  rcases Nat.even_or_odd (I.bundleSize p 0) with h0|h0 <;>
    rcases Nat.even_or_odd (I.bundleSize p 1) with h1|h1 <;>
    rcases Nat.even_or_odd (I.bundleSize p 2) with h2|h2
  · left;intro j;fin_cases j <;> assumption
  · right;right;refine ⟨0,?_⟩;rw [lineSize_eq];exact h0.add_odd h2
  · right;right;refine ⟨1,?_⟩;rw [lineSize_eq];exact h1.add_even h2
  · right;right;refine ⟨0,?_⟩;rw [lineSize_eq];exact h0.add_odd h2
  · right;right;refine ⟨0,?_⟩;rw [lineSize_eq];exact h0.add_even h2
  · right;right;refine ⟨1,?_⟩;rw [lineSize_eq];exact h1.add_odd h2
  · right;right;refine ⟨0,?_⟩;rw [lineSize_eq];exact h0.add_even h2
  · right;left;intro j;fin_cases j <;> assumption

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeRankTwoRegularize
end
