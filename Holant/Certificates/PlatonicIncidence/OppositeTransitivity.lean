import Holant.Certificates.PlatonicIncidence.OppositePhysical

/-! A common actual current-group operation carries any opposite-I rainbow to
any other, in the original ordered ports. The identity port permutation is
an explicit permissible witness; all scales are nonzero. -/
namespace Holant.Certificates.PlatonicIncidence.Opposite
open Holant Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
open Holant.Certificates.OppositeIcosahedral
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem opposite_inverse {U : BMat} (hU : Direction U) : Direction (U⁻¹ : BMat) := by
  obtain ⟨V,hV,rfl⟩ := (direction_iff_conjugate U).mp hU
  have hv : V.det≠0 := groupDirection_det_ne_zero .icosahedral hV
  have h1 : conjugate (1 : BMat)=1 := by simp [conjugate,D_Dinv]
  have he : (conjugate V)⁻¹=conjugate (V⁻¹ : BMat) := by
    apply Matrix.inv_eq_right_inv
    rw [←conjugate_mul,Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hv),h1]
  rw [he]
  exact conjugate_standard (direction_inverse .icosahedral hV)

theorem actual_transitivity (p q : Fin 3→Point) (hp : Rainbow p) (hq : Rainbow q) :
    ∃k : Fin 4→Fin 60,∃lam : Fin 3→ℂ,(∀r,lam r≠0) ∧
      ∀r,(physicalNetwork (p r).rep (representativeLegs k)).denote=lam r • (q r).rep := by
  obtain ⟨kp,ap,hap,hp⟩ := physical_normalization p hp
  obtain ⟨kq,aq,haq,hq⟩ := physical_normalization q hq
  let P := representativeLegs kp
  let Q := representativeLegs kq
  let L : Legs := fun j => (Q j)⁻¹*P j
  have hQ : ∀j,(Q j).det≠0 := fun j => Direction.det_ne_zero (oppositeRepresentative_mem (kq j))
  have hL : ∀j,Direction (L j) := fun j => Direction.mul
    (opposite_inverse (oppositeRepresentative_mem (kq j))) (oppositeRepresentative_mem (kp j))
  have hi (r : Fin 3) : act (fun j => (Q j)⁻¹) (initial r)=(aq r)⁻¹ • (q r).rep := by
    have hh := hq r
    rw [physicalNetwork_denote_act] at hh
    have ht := congrArg (act (fun j => (Q j)⁻¹)) hh
    change act (fun j => (Q j)⁻¹) (act Q (q r).rep)=
      act (fun j => (Q j)⁻¹) (aq r • initial r) at ht
    rw [act_inverse Q hQ,act_smul] at ht
    calc act (fun j => (Q j)⁻¹) (initial r)=
        (aq r)⁻¹ • (aq r • act (fun j => (Q j)⁻¹) (initial r)) := by simp [smul_smul,haq r]
      _=(aq r)⁻¹ • (q r).rep := by rw [←ht]
  have hact (r : Fin 3) : act L (p r).rep=(ap r*(aq r)⁻¹) • (q r).rep := by
    have hh := hp r
    rw [physicalNetwork_denote_act] at hh
    change act P (p r).rep=ap r • initial r at hh
    change act (fun j => (Q j)⁻¹*P j) (p r).rep=_
    rw [←act_comp,hh,act_smul,hi,smul_smul]
  have hd : ∀j,∃i : Fin 60,∃c : ℂ,c≠0 ∧ L j=c • oppositeRepresentative i :=
    fun j => (direction_complete _).mp (hL j)
  choose k c hc he using hd
  have hn : (∏j,c j)≠0 := Finset.prod_ne_zero_iff.mpr (fun j _ => hc j)
  have hlegs : L=(fun j => c j • representativeLegs k j) := funext he
  refine ⟨k,fun r => (∏j,c j)⁻¹*(ap r*(aq r)⁻¹),
    fun r => mul_ne_zero (inv_ne_zero hn) (mul_ne_zero (hap r) (inv_ne_zero (haq r))),?_⟩
  intro r
  have ht := hact r
  rw [hlegs,act_rescale_legs] at ht
  rw [physicalNetwork_denote_act]
  calc act (representativeLegs k) (p r).rep=
      (∏j,c j)⁻¹ • ((∏j,c j) • act (representativeLegs k) (p r).rep) := by simp [smul_smul,hn]
    _=_ := by rw [ht,smul_smul]

theorem actual_transitivity_resources (p q : Fin 3→Point) (hp : Rainbow p) (hq : Rainbow q) :
    ∃k : Fin 4→Fin 60,∃lam : Fin 3→ℂ,(∀r,lam r≠0) ∧
      ∀r,Gadget.Realizes (physicalFamily (p r).rep
        {B | ∃i : Fin 60,B=physicalSource (oppositeRepresentative i)})
          .disequality (lam r • (q r).rep) := by
  obtain ⟨k,lam,hlam,he⟩ := actual_transitivity p q hp hq
  refine ⟨k,lam,hlam,?_⟩
  intro r
  have hg := physical_realizes_of_source_mem (p r).rep
    {B | ∃i : Fin 60,B=physicalSource (oppositeRepresentative i)} (representativeLegs k)
    (fun j => ⟨k j,rfl⟩)
  rw [←physicalNetwork_denote_act,he r] at hg
  exact hg

end
end Holant.Certificates.PlatonicIncidence.Opposite
