import Holant.ReedMuller.Steiner.Blocks

namespace Holant.ReedMuller.Steiner
open Holant.ReedMuller.LowArity
noncomputable section
variable {n : ℕ}

/-- Three distinct base-block partners give distinct fourth points outside. -/
theorem extension_ne {D : BinaryCode n} (h : SteinerProperty D)
    {B : Finset (Fin n)} {a b c x y z : Fin n}
    (ha : a∈B) (hb : b∈B) (hbc : b≠c) (hba : b≠a)
    (hx : x∉B) (hy : y∉B) (hz : z∉B) (hyx : y≠x)
    (hC : Block D {a,b,x,y}) (hE : Block D {a,c,x,z}) : y≠z := by
  intro he
  subst z
  have hax : a≠x := by intro e; subst x; exact hx ha
  have hay : a≠y := by intro e; subst y; exact hy ha
  have hCE := block_eq h hC hE hax hay hyx.symm
    (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  have hbm : b∈({a,c,x,y}:Finset (Fin n)) := by rw [←hCE]; simp
  simp only [Finset.mem_insert,Finset.mem_singleton] at hbm
  rcases hbm with he | he | he | he
  · exact hba he
  · exact hbc he
  · exact hx (he ▸ hb)
  · exact hy (he ▸ hb)

structure Configuration (D : BinaryCode n) where
  points : Fin 8 ↪ Fin n
  block0 : Block D {points 0,points 1,points 2,points 3}
  block1 : Block D {points 0,points 1,points 4,points 5}
  block2 : Block D {points 0,points 2,points 4,points 6}
  block3 : Block D {points 0,points 3,points 4,points 7}

theorem configuration_exists (D : BinaryCode n) (hn : 4<n) (h : SteinerProperty D) :
    Nonempty (Configuration D) := by
  let a0 : Fin n := ⟨0,by omega⟩
  let a1 : Fin n := ⟨1,by omega⟩
  let a2 : Fin n := ⟨2,by omega⟩
  have h01 : a0≠a1 := by simp [a0,a1]
  have h02 : a0≠a2 := by simp [a0,a2]
  have h12 : a1≠a2 := by simp [a1,a2]
  obtain ⟨a3,h30,h31,h32,hB⟩ := fourth_point h a0 a1 a2 h01 h02 h12
  let B : Finset (Fin n) := {a0,a1,a2,a3}
  have hx : ∃ a4 : Fin n,a4∉B := by
    by_contra hnone
    push_neg at hnone
    have he : B=Finset.univ := by ext i; simp [hnone i]
    have hc := hB.1
    change B.card=4 at hc
    rw [he,Finset.card_univ,Fintype.card_fin] at hc
    omega
  obtain ⟨a4,h4⟩ := hx
  have h40 : a4≠a0 := by intro he; subst a4; exact h4 (by simp [B])
  have h41 : a4≠a1 := by intro he; subst a4; exact h4 (by simp [B])
  have h42 : a4≠a2 := by intro he; subst a4; exact h4 (by simp [B])
  have h43 : a4≠a3 := by intro he; subst a4; exact h4 (by simp [B])
  obtain ⟨a5,h50,h51,h54,hB1⟩ := fourth_point h a0 a1 a4 h01 h40.symm h41.symm
  obtain ⟨a6,h60,h62,h64,hB2⟩ := fourth_point h a0 a2 a4 h02 h40.symm h42.symm
  obtain ⟨a7,h70,h73,h74,hB3⟩ := fourth_point h a0 a3 a4 h30.symm h40.symm h43.symm
  have h5 : a5∉B := fourth_outside h hB (by simp [B]) (by simp [B]) h01 h4 h50 h51 hB1
  have h6 : a6∉B := fourth_outside h hB (by simp [B]) (by simp [B]) h02 h4 h60 h62 hB2
  have h7 : a7∉B := fourth_outside h hB (by simp [B]) (by simp [B]) h30.symm h4 h70 h73 hB3
  have h56 : a5≠a6 := extension_ne h (by simp [B]) (by simp [B]) h12 h01.symm h4 h5 h6 h54 hB1 hB2
  have h57 : a5≠a7 := extension_ne h (by simp [B]) (by simp [B]) h31.symm h01.symm h4 h5 h7 h54 hB1 hB3
  have h67 : a6≠a7 := extension_ne h (by simp [B]) (by simp [B]) h32.symm h02.symm h4 h6 h7 h64 hB2 hB3
  have h5all : a5≠a0 ∧ a5≠a1 ∧ a5≠a2 ∧ a5≠a3 := by simpa [B] using h5
  have h6all : a6≠a0 ∧ a6≠a1 ∧ a6≠a2 ∧ a6≠a3 := by simpa [B] using h6
  have h7all : a7≠a0 ∧ a7≠a1 ∧ a7≠a2 ∧ a7≠a3 := by simpa [B] using h7
  let p : Fin 8 → Fin n := ![a0,a1,a2,a3,a4,a5,a6,a7]
  have hp : Function.Injective p := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [p]
  refine ⟨⟨⟨p,hp⟩,?_,?_,?_,?_⟩⟩
  · simpa [p] using hB
  · simpa [p] using hB1
  · simpa [p] using hB2
  · simpa [p] using hB3

end
end Holant.ReedMuller.Steiner
