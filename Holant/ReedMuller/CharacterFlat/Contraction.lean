import Holant.ReedMuller.CharacterFlat.DoubleFiber
import Holant.ReedMuller.CharacterFlat.SingleFiber

/-! Full character-flat contraction: the real one- or two-lift sum is either
zero everywhere or a nonzero linear character on the projected self-dual coset. -/
namespace Holant.ReedMuller.CharacterFlat
open Holant Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

theorem close_character_selfDual (D : BinaryCode (n+2)) (hD : SelfDual D)
    (a : BinaryVector (n+2)) (ell : Character (n+2)) (c : ℂ) (hc : c≠0) (eta : ZMod 2) :
    closeValue eta (value c a D ell)=0 ∨
      ∃ (x0 : BinaryVector n) (c' : ℂ) (ell' : Character n),c'≠0 ∧
        closeValue eta (value c a D ell)=value c' x0 (equalProjection D) ell' ∧
        SelfDual (equalProjection D) := by
  by_cases hfeasible : ∃ b x,lift eta b x-a∈D
  · obtain ⟨b0,x0,h0⟩ := hfeasible
    by_cases hd : pairWord n∈D
    · by_cases hs : ell (pairWord n)=0
      · right
        refine ⟨x0,2*c*sign (ell (lift eta 0 0)),ell.comp tailEmbedding,
          double_scalar_nonzero c hc ell eta,?_,equalProjection_selfDual D hD⟩
        rw [close_with_pair D hd a ell c eta b0 x0 h0,if_pos hs]
      · left
        rw [close_with_pair D hd a ell c eta b0 x0 h0,if_neg hs]
    · obtain ⟨z,hz,hs⟩ := exists_section_word D hD hd
      right
      refine ⟨x0,c*sign (ell (lift eta b0 x0)-(ell.comp (sectionLinear (dropTwo z))) x0),
        ell.comp (sectionLinear (dropTwo z)),mul_ne_zero hc (sign_nonzero _),
        close_with_section D hD z hz hs a ell c eta b0 x0 h0,equalProjection_selfDual D hD⟩
  · left
    funext x
    apply Finset.sum_eq_zero
    intro b _
    have hm : lift eta b x-a∉D := fun h => hfeasible ⟨b,x,h⟩
    simp [value,hm]

theorem nonzeroFlat_contract (f : Signature ℂ (n+2)) (hf : NonzeroFlat f) (eta : ZMod 2) :
    CFlat (Signature.contract (parityKernel eta) f) := by
  obtain ⟨c,a,D,ell,hD,rfl⟩ := hf
  have he : Signature.contract (parityKernel eta) (signature c a D ell)=
      fun x => closeValue eta (value c a D ell) (vectorWord x) := by
    funext x
    exact closeValue_eq_contract eta (value c a D ell) x
  rw [he]
  rcases close_character_selfDual D hD a ell c c.ne_zero eta with hz | ⟨x0,c',ell',hc',he',hD'⟩
  · left
    rw [hz]
    rfl
  · right
    refine ⟨Units.mk0 c' hc',x0,equalProjection D,ell',hD',?_⟩
    funext x
    rw [he']
    rfl

theorem CFlat.contract (f : Signature ℂ (n+2)) (hf : CFlat f) (eta : ZMod 2) :
    CFlat (Signature.contract (parityKernel eta) f) := by
  rcases hf with rfl | hf
  · exact Or.inl (Signature.contract_zero _)
  · exact nonzeroFlat_contract f hf eta

end
end Holant.ReedMuller.CharacterFlat
