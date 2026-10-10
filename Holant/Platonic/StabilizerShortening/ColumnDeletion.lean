import Holant.Platonic.StabilizerErasure.SemanticFullSource
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-! Select a genuine column basis, then two different physical columns
outside it. The surviving computational coordinates remain injective. -/
namespace Holant.Platonic.StabilizerShortening
open Holant Holant.Tractable.AffinePhase
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.RadonAccess
open Holant.Platonic.StabilizerLine Holant.Platonic.StabilizerErasure
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {k n : ℕ}

theorem exists_two_deletable_columns (M : Matrix (Fin k) (Fin n) (ZMod 2))
    (hrank : M.rank=k) (hroom : k+2≤n) :
    ∃r s : Fin n,r≠s ∧ ∀z w : BinaryVector k,
      (∀j : Fin n,j≠r → j≠s → M.transpose.mulVec z j=M.transpose.mulVec w j) → z=w := by
  obtain ⟨ι,a,ha,hspan,hind⟩ := exists_linearIndependent' (ZMod 2) M.col
  letI : Fintype ι := Fintype.ofInjective a ha
  let B : Finset (Fin n) := Finset.univ.image a
  have hc : Fintype.card ι=k := by
    rw [←finrank_span_eq_card hind,hspan,←M.rank_eq_finrank_span_cols,hrank]
  have hB : B.card=k := by
    simp only [B,Finset.card_image_of_injective _ ha,Finset.card_univ,hc]
  have hroom' : 1<Bᶜ.card := by
    rw [Finset.card_compl,Fintype.card_fin,hB]
    omega
  obtain ⟨r,hr,s,hs,hrs⟩ := Finset.one_lt_card.mp hroom'
  have htop : Submodule.span (ZMod 2) (Set.range (M.col ∘ a))=⊤ := by
    rw [hspan]
    apply Submodule.eq_top_of_finrank_eq
    simpa only [←M.rank_eq_finrank_span_cols,Module.finrank_pi,Fintype.card_fin] using hrank
  refine ⟨r,s,hrs,?_⟩
  intro z w he
  have hd : dotBilinear z=dotBilinear w := by
    apply LinearMap.ext_on_range htop
    intro i
    have hia : a i∈B := by simp [B]
    have hir : a i≠r := by intro h;subst r;exact (Finset.mem_compl.mp hr) hia
    have his : a i≠s := by intro h;subst s;exact (Finset.mem_compl.mp hs) hia
    have h := he (a i) hir his
    simpa [dotBilinear_apply,Holant.ReedMuller.LowArity.dot,Matrix.mulVec,
      dotProduct,Matrix.col,Function.comp_def,mul_comm] using h
  ext i
  have h := congrArg (fun L : BinaryVector k →ₗ[ZMod 2] ZMod 2=>L (unitWord i)) hd
  simpa only [dotBilinear_apply,dot_unit_right] using h

end
end Holant.Platonic.StabilizerShortening
