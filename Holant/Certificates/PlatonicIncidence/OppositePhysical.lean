import Holant.Certificates.PlatonicIncidence.OppositeOrbit

/-! Actual opposite-icosahedral port normalization. The coefficient map D is
never used as a physical resource: every inserted binary is in the literal
current group, with fixed representative indices and explicit nonzero scales. -/
namespace Holant.Certificates.PlatonicIncidence.Opposite
open Holant Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
open Holant.Certificates.OppositeIcosahedral
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def currentLegs (L : Legs) : Legs := fun j => conjugate (L j)

theorem currentLegs_intertwine (L : Legs) (F : FourTensor) :
    act (currentLegs L) (act legs F)=act legs (act L F) := by
  rw [act_comp,act_comp]
  congr 1
  funext j
  simp only [currentLegs,legs,conjugate,mul_assoc,Dinv_D,mul_one]

theorem transpose_conjugate (U : BMat) :
    (conjugate U).transpose=(-1 : ℂ) • conjugate ((Matrix.of Q3)*U.transpose*(Matrix.of Q3)) := by
  ext a b
  cases a <;> cases b <;>
    simp [conjugate,D,Dinv,Q0,Q3,Signature.equality,Matrix.mul_apply,Matrix.smul_apply] <;>
    ring_nf <;> simp [Complex.I_sq] <;> ring

theorem opposite_transpose {U : BMat} (hU : Direction U) : Direction U.transpose := by
  obtain ⟨V,hV,rfl⟩ := (direction_iff_conjugate U).mp hU
  rw [transpose_conjugate]
  apply Direction.smul _ (by norm_num)
  apply conjugate_standard
  have hQ : groupDirection .icosahedral (Matrix.of Q3) := quaternion_axis_direction .icosahedral 3
  exact RainbowOrbit.groupDirection_mul .icosahedral
    (RainbowOrbit.groupDirection_mul .icosahedral hQ (direction_transpose .icosahedral hV)) hQ

theorem physical_source_mem (i : Fin 60) :
    Direction (physicalSource (oppositeRepresentative i)) ∧
    Direction (physicalSource (oppositeRepresentative i)*OppositeIcosahedral.X) := by
  have h := Direction.mul direction_X (opposite_transpose (oppositeRepresentative_mem i))
  exact ⟨h,(transfer_iff _).mpr h⟩

def representativeLegs (k : Fin 4→Fin 60) : Legs := fun j => oppositeRepresentative (k j)

def initial (r : Fin 3) : FourTensor := act legs (base r)

theorem inverse_word (t : OrbitIndex .icosahedral) :
    ∃k : Fin 4→Fin 60,∃c : Fin 4→ℂ,(∀j,c j≠0) ∧
      (∀j,currentLegs (fun j => (RainbowOrbit.orbitLegs .icosahedral t j)⁻¹) j=
        c j • representativeLegs k j) ∧
      ∀r,act (representativeLegs k)
        (act legs (act (RainbowOrbit.orbitLegs .icosahedral t) (base r)))=
          (∏j,c j)⁻¹ • initial r := by
  let L : Legs := fun j => (RainbowOrbit.orbitLegs .icosahedral t j)⁻¹
  have hL : GroupLegs .icosahedral L := (orbitLegs_mem .icosahedral t).inverse
  have hd : ∀j,∃i : Fin 60,∃c : ℂ,c≠0 ∧ currentLegs L j=c • oppositeRepresentative i :=
    fun j => (direction_complete _).mp (conjugate_standard (hL j))
  choose k c hc he using hd
  refine ⟨k,c,hc,he,?_⟩
  intro r
  have hh := currentLegs_intertwine L (act (RainbowOrbit.orbitLegs .icosahedral t) (base r))
  have hlegs : currentLegs L=(fun j => c j • representativeLegs k j) := funext he
  rw [hlegs,act_rescale_legs] at hh
  have hi : act L (act (RainbowOrbit.orbitLegs .icosahedral t) (base r))=base r :=
    act_inverse _ (orbitLegs_mem .icosahedral t).det _
  rw [hi] at hh
  have hn : (∏j,c j)≠0 := Finset.prod_ne_zero_iff.mpr (fun j _ => hc j)
  calc act (representativeLegs k) (act legs (act (RainbowOrbit.orbitLegs .icosahedral t) (base r)))=
      (∏j,c j)⁻¹ • ((∏j,c j) •
        act (representativeLegs k) (act legs (act (RainbowOrbit.orbitLegs .icosahedral t) (base r)))) := by
          simp [smul_smul,hn]
    _=(∏j,c j)⁻¹ • initial r := by rw [hh]; rfl

theorem physical_normalization (p : Fin 3→Point) (hp : Rainbow p) :
    ∃k : Fin 4→Fin 60,∃lam : Fin 3→ℂ,(∀r,lam r≠0) ∧
      ∀r,(physicalNetwork (p r).rep (representativeLegs k)).denote=lam r • initial r := by
  obtain ⟨t,rfl⟩ := rainbow_enumerated p hp
  obtain ⟨k,c,hc,he,hi⟩ := inverse_word t
  have hn : (∏j,c j)≠0 := Finset.prod_ne_zero_iff.mpr (fun j _ => hc j)
  have ha : ∀r,∃a : ℂ,a≠0 ∧ (orbitPoint t r).rep=
      a • act legs (act (RainbowOrbit.orbitLegs .icosahedral t) (base r)) := by
    intro r
    obtain ⟨a,ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ
      (act legs (act (RainbowOrbit.orbitLegs .icosahedral t) (base r)))
      (act_nonzero _ legs_det (act_nonzero _ (orbitLegs_mem .icosahedral t).det (base_nonzero r)))
    exact ⟨a,Units.ne_zero a,ha.symm⟩
  choose a ha hrep using ha
  refine ⟨k,fun r => a r*(∏j,c j)⁻¹,fun r => mul_ne_zero (ha r) (inv_ne_zero hn),?_⟩
  intro r
  rw [physicalNetwork_denote_act,hrep r,act_smul,hi r,smul_smul]

theorem physical_resources (p : Fin 3→Point) (hp : Rainbow p) :
    ∃k : Fin 4→Fin 60,∃lam : Fin 3→ℂ,(∀r,lam r≠0) ∧
      ∀r,Gadget.Realizes (physicalFamily (p r).rep
        {B | ∃i : Fin 60,B=physicalSource (oppositeRepresentative i)})
          .disequality (lam r • initial r) := by
  obtain ⟨k,lam,hlam,he⟩ := physical_normalization p hp
  refine ⟨k,lam,hlam,?_⟩
  intro r
  have hg := physical_realizes_of_source_mem (p r).rep
    {B | ∃i : Fin 60,B=physicalSource (oppositeRepresentative i)} (representativeLegs k)
    (fun j => ⟨k j,rfl⟩)
  rw [←physicalNetwork_denote_act,he r] at hg
  exact hg

end
end Holant.Certificates.PlatonicIncidence.Opposite
