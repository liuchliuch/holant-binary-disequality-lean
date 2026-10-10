import Holant.Certificates.RainbowOrbit.OrbitCompleteness
import Holant.Certificates.RainbowOrbit.PhysicalSingleLeg

namespace Holant.Certificates.RainbowOrbit
open Holant Holant.Certificates.MatchingProductBridge
noncomputable section
set_option backward.isDefEq.respectTransparency false

def representativeLegs (g : PlatonicModel) (k : Fin 4→Fin (size g)) : Legs :=
  fun j => representative g (k j)

/-- The inverse coset tuple is converted to the fixed actual representatives;
its scalar is the reciprocal of the recorded product of four leg scales. -/
theorem inverse_word (g : PlatonicModel) (t : OrbitIndex g) :
    ∃k : Fin 4→Fin (size g),∃c : Fin 4→ℂ,(∀j,c j≠0) ∧
      (∀j,(orbitLegs g t j)⁻¹=c j • representative g (k j)) ∧
      ∀r,act (representativeLegs g k) (act (orbitLegs g t) (base r))=(∏j,c j)⁻¹ • base r := by
  have hh : ∀j,∃k : Fin (size g),∃c : ℂ,c≠0 ∧
      (orbitLegs g t j)⁻¹=c • representative g k :=
    fun j => (complete g _).mp (direction_inverse g (orbitLegs_mem g t j))
  choose k c hc he using hh
  refine ⟨k,c,hc,he,?_⟩
  intro r
  have hi := act_inverse (orbitLegs g t) (orbitLegs_mem g t).det (base r)
  have hlegs : (fun j => (orbitLegs g t j)⁻¹)=(fun j => c j • representativeLegs g k j) := funext he
  rw [hlegs,act_rescale_legs] at hi
  have hn : (∏j,c j)≠0 := Finset.prod_ne_zero_iff.mpr (fun j _ => hc j)
  calc act (representativeLegs g k) (act (orbitLegs g t) (base r))=
      (∏j,c j)⁻¹ • ((∏j,c j) • act (representativeLegs g k) (act (orbitLegs g t) (base r))) := by
        simp [smul_smul,hn]
    _=(∏j,c j)⁻¹ • base r := by rw [hi]

/-- A finite actual native-X normalization witness for each semantic rainbow.
The original four boundary ports retain their order. -/
theorem rainbow_physical_normalization (g : PlatonicModel) (p : Fin 3→Point) (hp : Rainbow g p) :
    ∃k : Fin 4→Fin (size g),∃lam : Fin 3→ℂ,(∀r,lam r≠0) ∧
      ∀r,(physicalNetwork (p r).rep (representativeLegs g k)).denote=lam r • base r := by
  obtain ⟨t,rfl⟩ := rainbow_enumerated g p hp
  obtain ⟨k,c,hc,he,hi⟩ := inverse_word g t
  have hn : (∏j,c j)≠0 := Finset.prod_ne_zero_iff.mpr (fun j _ => hc j)
  have ha : ∀r,∃a : ℂ,a≠0 ∧ (orbitPoint g t r).rep=a • act (orbitLegs g t) (base r) := by
    intro r
    obtain ⟨a,ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ
      (act (orbitLegs g t) (base r)) (act_nonzero _ (orbitLegs_mem g t).det (base_nonzero r))
    exact ⟨a,Units.ne_zero a,ha.symm⟩
  choose a ha hrep using ha
  refine ⟨k,fun r => a r*(∏j,c j)⁻¹,fun r => mul_ne_zero (ha r) (inv_ne_zero hn),?_⟩
  intro r
  rw [physicalNetwork_denote_act,hrep r,act_smul,hi r,smul_smul]

/-- The fixed representative source binaries in this theorem are exactly the
four concrete resources of the normalization network. -/
theorem rainbow_physical_resources (g : PlatonicModel) (p : Fin 3→Point) (hp : Rainbow g p) :
    ∃k : Fin 4→Fin (size g),∃lam : Fin 3→ℂ,(∀r,lam r≠0) ∧
      ∀r,Gadget.Realizes (physicalFamily (p r).rep
        {B | ∃i : Fin (size g),B=physicalSource (representative g i)}) .disequality (lam r • base r) := by
  obtain ⟨k,lam,hlam,he⟩ := rainbow_physical_normalization g p hp
  refine ⟨k,lam,hlam,?_⟩
  intro r
  have hg := physical_realizes_of_source_mem (p r).rep
    {B | ∃i : Fin (size g),B=physicalSource (representative g i)} (representativeLegs g k)
    (fun j => ⟨k j,rfl⟩)
  rw [←physicalNetwork_denote_act,he r] at hg
  exact hg

end
end Holant.Certificates.RainbowOrbit
