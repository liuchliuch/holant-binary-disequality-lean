import Holant.Platonic.StabilizerLine.BlockInversion

/-! Construct adapted coordinates from the actual support subspace. -/
namespace Holant.Platonic.StabilizerLine
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.AffinePatching
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n r s : ℕ}

theorem exists_adapted_coordinates (D : BinaryCode n) :
    ∃ r s : ℕ,∃ e : BinaryVector n ≃ₗ[ZMod 2] BinaryVector r×BinaryVector s,
      r=Module.finrank (ZMod 2) D ∧ r+s=n ∧ ∀ x,(e x).2=0 ↔ x∈D := by
  obtain ⟨C,hC⟩ := D.exists_isCompl
  let ed := (Module.finBasis (ZMod 2) D).equivFun
  let ec := (Module.finBasis (ZMod 2) C).equivFun
  let e := (D.prodEquivOfIsCompl C hC).symm.trans (ed.prodCongr ec)
  refine ⟨_,_,e,rfl,?_,?_⟩
  · simpa [BinaryVector] using Submodule.finrank_add_eq_of_isCompl hC
  · intro x
    change ec ((D.prodEquivOfIsCompl C hC).symm x).2=0 ↔ x∈D
    rw [ec.map_eq_zero_iff]
    exact D.prodEquivOfIsCompl_symm_apply_snd_eq_zero C hC

theorem blockWalsh_indicator (D : BinaryCode n)
    (e : BinaryVector n ≃ₗ[ZMod 2] BinaryVector r×BinaryVector s)
    (he : ∀ x,(e x).2=0 ↔ x∈D) (c : ℂ) :
    blockWalsh e (fun x => if vectorWord x∈D then c else 0)=
      fun x => ((sqrtTwo⁻¹^r:AlgebraicComplex):ℂ)*(2:ℂ)^r*c*delta x := by
  funext x
  have hmem (t : Word r) : vectorWord (blockWord e t x)∈D ↔ (e (vectorWord x)).2=0 := by
    rw [←he,blockWord_coordinates]
  simp only [blockWalsh,hmem]
  by_cases hr : (e (vectorWord x)).2=0
  · simp only [hr,ite_true]
    rw [←Finset.sum_mul]
    have hs : (∑ t : Word r,(walshKernel (wordVector ((e (vectorWord x)).1)) t:ℂ))=
        if (e (vectorWord x)).1=0 then (2:ℂ)^r else 0 := by
      have h := congrArg (fun a : AlgebraicComplex => (a:ℂ))
        (walshKernel_sum (wordVector ((e (vectorWord x)).1)))
      have hz : wordVector ((e (vectorWord x)).1)=origin r ↔ (e (vectorWord x)).1=0 := by
        constructor
        · intro hh;simpa using congrArg vectorWord hh
        · intro hh;rw [hh];rfl
      simp only [hz] at h
      by_cases hz0 : (e (vectorWord x)).1=0
      · rw [if_pos hz0] at h ⊢
        push_cast at h
        exact h
      · rw [if_neg hz0] at h ⊢
        push_cast at h
        exact h
    rw [hs]
    have hz : (e (vectorWord x)).1=0 ↔ x=origin n := by
      constructor
      · intro h
        have hx : vectorWord x=0 := e.injective (by rw [map_zero];exact Prod.ext h hr)
        apply vector_injective
        simpa only [vector_origin] using hx
      · intro h;subst x;simp
    simp only [delta,←hz]
    split_ifs <;> ring
  · simp only [hr,ite_false,mul_zero,Finset.sum_const_zero]
    have hx : x≠origin n := by intro h;subst x;exact hr (by simp)
    simp [delta,hx]

end
end Holant.Platonic.StabilizerLine
