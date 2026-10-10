import Holant.Proofs.FiniteGroups.Stabilization.ExactElementOrders
import Holant.Proofs.FiniteGroups.Stabilization.ActualGroups
import Holant.Proofs.FiniteGroups.UniqueType


namespace Holant.LocalDrafts.FinitePGL2.Stabilization

open Holant.Projective.BoundedTorsion
open Holant.Projective.FiniteSubgroupClassification
open Holant.Projective.FiniteGroupFacts
open Holant.Certificates.RainbowOrbit
noncomputable section

def sourceGroupBound (D : ℕ) : ℕ := max (2 * torsionExponent D) 60

/-- This intermediate estimate consumes pointwise element orders, not a
classification or group-cardinality conclusion.  Classification is invoked
inside the proof. -/
theorem complex_subgroup_card_le (H : Subgroup (PGL2 ℂ)) [Finite H]
    (e : ℕ) (horders : ∀ x : H, orderOf x ≤ e) : Nat.card H ≤ max (2 * e) 60 := by
  obtain ⟨t, ht⟩ := exists_model H
  cases t with
  | cyclic m =>
      obtain ⟨hm, ω, hω, hc⟩ := ht
      obtain ⟨iso⟩ := hc.nonempty_mulEquiv
      letI : IsCyclic H := iso.isCyclic.mpr (cyclicModel_isCyclic ω)
      obtain ⟨x, hx⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp (inferInstance : IsCyclic H)
      have hb := horders x
      rw [hx] at hb
      exact (hb.trans (by omega : e ≤ 2 * e)).trans (le_max_left _ _)
  | dihedral m =>
      obtain ⟨hm, ω, hω, hc⟩ := ht
      obtain ⟨iso⟩ := hc.nonempty_mulEquiv
      obtain ⟨x, hx⟩ := dihedralModel_exists_order hω
      have hb := horders (iso.symm x)
      rw [iso.symm.orderOf_eq, hx] at hb
      have hn : Nat.card H = 2 * m := hc.card_eq.trans (dihedralModel_card hω)
      rw [hn]
      exact (Nat.mul_le_mul_left 2 hb).trans (le_max_left _ _)
  | platonic p =>
      have hn := ht.card_eq
      rw [modelPGL_card] at hn
      have hb : Nat.card H ≤ 60 := by cases p <;> norm_num [size] at hn ⊢ <;> omega
      exact hb.trans (le_max_right _ _)

variable {L : Type*} [Field L] [NumberField L]

/-- The frozen number-field subgroup has precisely the source bound.  An
embedding into C is constructed, not demanded as an unproved input. -/
theorem finite_subgroup_card_le_sourceBound (H : Subgroup (PGL2 L)) [Finite H] :
    Nat.card H ≤ sourceGroupBound (Module.finrank ℚ L) := by
  let ι : L →ₐ[ℚ] ℂ := IsAlgClosed.lift
  let HC := H.map (pglExtend ι.toRingHom)
  let iso : H ≃* HC := H.equivMapOfInjective (pglExtend ι.toRingHom) (pglExtend_injective ι.toRingHom)
  letI : Finite HC := Finite.of_equiv H iso.toEquiv
  have hb := complex_subgroup_card_le HC (torsionExponent (Module.finrank ℚ L)) (by
    intro x
    let y := iso.symm x
    have hfin : IsOfFinOrder (y : PGL2 L) := H.subtype.isOfFinOrder (isOfFinOrder_of_finite y)
    have hd := projective_order_dvd_sourceExponent ι (y : PGL2 L) hfin
    have hle := Nat.le_of_dvd (torsionExponent_pos (Module.finrank ℚ L)) hd
    have he : orderOf x = orderOf (y : PGL2 L) := by
      rw [Subgroup.orderOf_coe]
      exact (iso.symm.orderOf_eq x).symm
    rwa [← he] at hle)
  change Nat.card (H.map (pglExtend ι.toRingHom)) ≤ _ at hb
  rw [pglExtend_card] at hb
  exact hb

theorem completeGroup_card_le_sourceBound (F : SignatureFamily L) (hτ : ResidualTorsion F) :
    Nat.card (completeGroup F hτ) ≤ sourceGroupBound (Module.finrank ℚ L) := by
  letI := completeGroup_finite F hτ
  exact finite_subgroup_card_le_sourceBound _

def sourceGroupDefect (F : SignatureFamily L) (hτ : ResidualTorsion F) : ℕ :=
  sourceGroupBound (Module.finrank ℚ L) - Nat.card (completeGroup F hτ)

theorem sourceGroupDefect_lt_of_strict {F G : SignatureFamily L}
    (hF : ResidualTorsion F) (hG : ResidualTorsion G)
    (h : completeGroup F hF < completeGroup G hG) :
    sourceGroupDefect G hG < sourceGroupDefect F hF := by
  letI := completeGroup_finite G hG
  have hc := Subgroup.card_lt_of_lt h
  have hb := completeGroup_card_le_sourceBound G hG
  unfold sourceGroupDefect
  omega

end
end Holant.LocalDrafts.FinitePGL2.Stabilization
