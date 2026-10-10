import Holant.ReedMuller.CoefficientAtlas.Code
import Mathlib.Data.Finset.Card

namespace Holant.ReedMuller.Steiner
open Holant.ReedMuller.LowArity
open scoped BigOperators
noncomputable section
variable {n : ℕ}

def indicator (B : Finset (Fin n)) : BinaryVector n := fun i => if i∈B then 1 else 0

def support (x : BinaryVector n) : Finset (Fin n) := Finset.univ.filter fun i => x i≠0

theorem indicator_support (x : BinaryVector n) : indicator (support x)=x := by
  funext i
  have hi : x i=0 ∨ x i=1 := by
    have h : ∀ a : ZMod 2,a=0 ∨ a=1 := by decide
    exact h (x i)
  rcases hi with hi | hi <;> simp [indicator,support,hi]

theorem support_indicator (B : Finset (Fin n)) : support (indicator B)=B := by
  ext i
  simp [support,indicator]

def Block (D : BinaryCode n) (B : Finset (Fin n)) : Prop := B.card=4 ∧ indicator B∈D

def SteinerProperty (D : BinaryCode n) : Prop :=
  ∀ a b c : Fin n,a≠b → a≠c → b≠c →
    ∃! B : Finset (Fin n),Block D B ∧ a∈B ∧ b∈B ∧ c∈B

theorem block_eq {D : BinaryCode n} (h : SteinerProperty D)
    {B C : Finset (Fin n)} (hB : Block D B) (hC : Block D C)
    {a b c : Fin n} (hab : a≠b) (hac : a≠c) (hbc : b≠c)
    (haB : a∈B) (hbB : b∈B) (hcB : c∈B)
    (haC : a∈C) (hbC : b∈C) (hcC : c∈C) : B=C := by
  obtain ⟨S,hs,hu⟩ := h a b c hab hac hbc
  exact (hu B ⟨hB,haB,hbB,hcB⟩).trans (hu C ⟨hC,haC,hbC,hcC⟩).symm

theorem fourth_point {D : BinaryCode n} (h : SteinerProperty D)
    (a b c : Fin n) (hab : a≠b) (hac : a≠c) (hbc : b≠c) :
    ∃ d : Fin n,d≠a ∧ d≠b ∧ d≠c ∧ Block D {a,b,c,d} := by
  obtain ⟨B,hB,_⟩ := h a b c hab hac hbc
  have ht : ({a,b,c}:Finset (Fin n)) ⊆ B := by
    intro i hi
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · exact hB.2.1
    · exact hB.2.2.1
    · exact hB.2.2.2
  have hc3 : ({a,b,c}:Finset (Fin n)).card=3 := by simp [hab,hac,hbc]
  have hdcard : (B \ {a,b,c}).card=1 := by rw [Finset.card_sdiff_of_subset ht,hB.1.1,hc3]
  obtain ⟨d,hd⟩ := Finset.card_eq_one.mp hdcard
  have hdm : d∈B \ {a,b,c} := by rw [hd]; simp
  have hdn : d∉({a,b,c}:Finset (Fin n)) := (Finset.mem_sdiff.mp hdm).2
  have hdi : d≠a ∧ d≠b ∧ d≠c := by simpa using hdn
  have he : B={a,b,c,d} := by
    have hu := Finset.sdiff_union_of_subset ht
    rw [hd] at hu
    ext i
    have hi := Finset.ext_iff.mp hu i
    simpa [or_assoc,or_comm,or_left_comm] using hi.symm
  exact ⟨d,hdi.1,hdi.2.1,hdi.2.2,he ▸ hB.1⟩

/-- A new block through two old points and one outside point has its fourth
point outside the old block; uniqueness through triples proves this directly. -/
theorem fourth_outside {D : BinaryCode n} (h : SteinerProperty D)
    {B : Finset (Fin n)} (hB : Block D B) {a b x y : Fin n}
    (ha : a∈B) (hb : b∈B) (hab : a≠b) (hx : x∉B)
    (hya : y≠a) (hyb : y≠b) (hC : Block D {a,b,x,y}) : y∉B := by
  intro hy
  have he := block_eq h hB hC hab hya.symm hyb.symm ha hb hy (by simp) (by simp) (by simp)
  apply hx
  rw [he]
  simp

end
end Holant.ReedMuller.Steiner
