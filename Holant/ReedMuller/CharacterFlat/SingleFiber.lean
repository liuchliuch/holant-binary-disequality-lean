import Holant.ReedMuller.CharacterFlat.LinearLift

/-! A self-dual code missing the contracted pair word has a literal linear
section determined by an actual codeword. Thus its unique fibre character
is an explicitly recorded affine boundary character. -/
namespace Holant.ReedMuller.CharacterFlat
open Holant Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

theorem exists_section_word (D : BinaryCode (n+2)) (hD : SelfDual D) (hd : pairWord n∉D) :
    ∃ z,z∈D ∧ z 0+z 1=1 := by
  have hz : ∃ z,z∈D ∧ dot (pairWord n) z≠0 := by
    by_contra h
    apply hd
    apply (hD _).mpr
    intro z hz
    by_contra hn
    exact h ⟨z,hz,hn⟩
  obtain ⟨z,hz,hn⟩ := hz
  rw [dot_pairWord] at hn
  exact ⟨z,hz,(by decide : ∀ t : ZMod 2,t≠0 → t=1) _ hn⟩

theorem prepend_mem_section (D : BinaryCode (n+2)) (hD : SelfDual D)
    (z : BinaryVector (n+2)) (hz : z∈D) (hs : z 0+z 1=1)
    (b : ZMod 2) (x : BinaryVector n) :
    prepend b x∈D ↔ x∈equalProjection D ∧ b=dot x (dropTwo z) := by
  have hb (b : ZMod 2) (hb : prepend b x∈D) : b=dot x (dropTwo z) := by
    have H := (hD _).mp hb z hz
    rw [dot_prepend_arbitrary,hs,mul_one] at H
    exact (add_eq_zero_iff _ _).mp H
  constructor
  · intro h
    exact ⟨⟨b,h⟩,hb b h⟩
  · rintro ⟨⟨r,hr⟩,h⟩
    have he : b=r := h.trans (hb r hr).symm
    rwa [he]

def chosenBit (b0 : ZMod 2) (z x0 x : BinaryVector n) : ZMod 2 := dot (x-x0) z+b0

theorem lift_mem_unique (D : BinaryCode (n+2)) (hD : SelfDual D)
    (z : BinaryVector (n+2)) (hz : z∈D) (hs : z 0+z 1=1)
    (a : BinaryVector (n+2)) (eta b0 : ZMod 2) (x0 : BinaryVector n)
    (h0 : lift eta b0 x0-a∈D) (b : ZMod 2) (x : BinaryVector n) :
    lift eta b x-a∈D ↔ x-x0∈equalProjection D ∧ b=chosenBit b0 (dropTwo z) x0 x := by
  rw [lift_mem_translate D a eta b0 x0 h0,prepend_mem_section D hD z hz hs]
  exact and_congr_right (fun _ => sub_eq_iff_eq_add)

theorem chosen_lift (eta b0 : ZMod 2) (z x0 x : BinaryVector n) :
    lift eta (chosenBit b0 z x0 x) x=sectionLinear z (x-x0)+lift eta b0 x0 := by
  have H := lift_affine_difference eta (chosenBit b0 z x0 x) b0 x x0 (0 : BinaryVector (n+2))
  simpa [chosenBit,sectionLinear] using H

theorem chosen_character (ell : Character (n+2)) (eta b0 : ZMod 2) (z x0 x : BinaryVector n) :
    ell (lift eta (chosenBit b0 z x0 x) x)=
      (ell (lift eta b0 x0)-(ell.comp (sectionLinear z)) x0)+(ell.comp (sectionLinear z)) x := by
  rw [chosen_lift,map_add]
  change (ell.comp (sectionLinear z)) (x-x0)+ell (lift eta b0 x0)=_
  rw [map_sub]
  ring

/-- The unique internal lift gives a uniform nonzero boundary character,
with its affine constant included in the output scalar. -/
theorem close_with_section (D : BinaryCode (n+2)) (hD : SelfDual D)
    (z : BinaryVector (n+2)) (hz : z∈D) (hs : z 0+z 1=1)
    (a : BinaryVector (n+2)) (ell : Character (n+2)) (c : ℂ)
    (eta b0 : ZMod 2) (x0 : BinaryVector n) (h0 : lift eta b0 x0-a∈D) :
    closeValue eta (value c a D ell)=
      value (c*sign (ell (lift eta b0 x0)-(ell.comp (sectionLinear (dropTwo z))) x0))
        x0 (equalProjection D) (ell.comp (sectionLinear (dropTwo z))) := by
  funext x
  simp only [closeValue,value,lift_mem_unique D hD z hz hs a eta b0 x0 h0]
  by_cases hx : x-x0∈equalProjection D
  · simp only [hx,true_and,ite_true]
    simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    rw [chosen_character,sign_add]
    ring
  · simp [hx]

end
end Holant.ReedMuller.CharacterFlat
