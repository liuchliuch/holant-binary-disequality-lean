import Holant.Certificates.RainbowOrbit.MarkedGenerators
import Holant.Certificates.RainbowOrbit.InitialLines

namespace Holant.Certificates.RainbowOrbit
open Holant Holant.Certificates.MatchingProductBridge
open OctahedralSeparator
noncomputable section
set_option backward.isDefEq.respectTransparency false

def markedRepresentativeLegs (f : Form) (k : Fin 4→Fin 24) : Legs :=
  fun j => complexMatrix (theta f (standard (k j)))

theorem marked_inverse_word (f : Form) (t : OrbitIndex .octahedral) :
    ∃k : Fin 4→Fin 24,∃c : Fin 4→ℂ,(∀j,c j≠0) ∧
      (∀j,currentLegs f (fun j => (orbitLegs .octahedral t j)⁻¹) j=
        c j • markedRepresentativeLegs f k j) ∧
      ∀r,act (markedRepresentativeLegs f k)
        (act (markLegs f) (act (orbitLegs .octahedral t) (base r)))=
          (∏j,c j)⁻¹ • markedInitial f r := by
  let L : Legs := fun j => (orbitLegs .octahedral t j)⁻¹
  have hL : GroupLegs .octahedral L := (orbitLegs_mem .octahedral t).inverse
  obtain ⟨k,c,hc,he⟩ := currentLegs_representatives f L hL
  refine ⟨k,c,hc,he,?_⟩
  intro r
  have hh := currentLegs_intertwine f L (act (orbitLegs .octahedral t) (base r))
  have hlegs : currentLegs f L=(fun j => c j • markedRepresentativeLegs f k j) := funext he
  rw [hlegs,act_rescale_legs] at hh
  have hi : act L (act (orbitLegs .octahedral t) (base r))=base r :=
    act_inverse _ (orbitLegs_mem .octahedral t).det _
  rw [hi] at hh
  have hn : (∏j,c j)≠0 := Finset.prod_ne_zero_iff.mpr (fun j _ => hc j)
  calc act (markedRepresentativeLegs f k) (act (markLegs f) (act (orbitLegs .octahedral t) (base r)))=
      (∏j,c j)⁻¹ • ((∏j,c j) •
        act (markedRepresentativeLegs f k) (act (markLegs f) (act (orbitLegs .octahedral t) (base r)))) := by
          simp [smul_smul,hn]
    _=(∏j,c j)⁻¹ • markedInitial f r := by rw [hh]; rfl

theorem marked_rainbow_physical_normalization (f : Form) (p : Fin 3→Point) (hp : MarkedRainbow f p) :
    ∃k : Fin 4→Fin 24,∃lam : Fin 3→ℂ,(∀r,lam r≠0) ∧
      ∀r,(physicalNetwork (p r).rep (markedRepresentativeLegs f k)).denote=lam r • markedInitial f r := by
  obtain ⟨t,rfl⟩ := marked_rainbow_enumerated f p hp
  obtain ⟨k,c,hc,he,hi⟩ := marked_inverse_word f t
  have hn : (∏j,c j)≠0 := Finset.prod_ne_zero_iff.mpr (fun j _ => hc j)
  have ha : ∀r,∃a : ℂ,a≠0 ∧ (markedOrbitPoint f t r).rep=
      a • act (markLegs f) (act (orbitLegs .octahedral t) (base r)) := by
    intro r
    obtain ⟨a,ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ
      (act (markLegs f) (act (orbitLegs .octahedral t) (base r)))
      (act_nonzero _ (markLegs_det f) (act_nonzero _ (orbitLegs_mem .octahedral t).det (base_nonzero r)))
    exact ⟨a,Units.ne_zero a,ha.symm⟩
  choose a ha hrep using ha
  refine ⟨k,fun r => a r*(∏j,c j)⁻¹,fun r => mul_ne_zero (ha r) (inv_ne_zero hn),?_⟩
  intro r
  rw [physicalNetwork_denote_act,hrep r,act_smul,hi r,smul_smul]

theorem marked_rainbow_physical_resources (f : Form) (p : Fin 3→Point) (hp : MarkedRainbow f p) :
    ∃k : Fin 4→Fin 24,∃lam : Fin 3→ℂ,(∀r,lam r≠0) ∧
      ∀r,Gadget.Realizes (physicalFamily (p r).rep
        {B | ∃i : Fin 24,B=physicalSource (complexMatrix (theta f (standard i)))})
          .disequality (lam r • markedInitial f r) := by
  obtain ⟨k,lam,hlam,he⟩ := marked_rainbow_physical_normalization f p hp
  refine ⟨k,lam,hlam,?_⟩
  intro r
  have hg := physical_realizes_of_source_mem (p r).rep
    {B | ∃i : Fin 24,B=physicalSource (complexMatrix (theta f (standard i)))} (markedRepresentativeLegs f k)
    (fun j => ⟨k j,rfl⟩)
  rw [←physicalNetwork_denote_act,he r] at hg
  exact hg

theorem prime_rainbow_physical_normalization (p : Fin 3→Point) (hp : MarkedRainbow 1 p) :
    ∃k : Fin 4→Fin 24,∃lam : Fin 3→ℂ,(∀r,lam r≠0) ∧
      ∀r,(physicalNetwork (p r).rep (markedRepresentativeLegs 1 k)).denote=lam r • primeInitial r := by
  obtain ⟨k,lam,hlam,he⟩ := marked_rainbow_physical_normalization 1 p hp
  refine ⟨k,fun r => lam r*primeScale r,fun r => mul_ne_zero (hlam r) (primeScale_ne_zero r),?_⟩
  intro r
  rw [he r,markedInitial,prime_initial_exact,smul_smul]

end
end Holant.Certificates.RainbowOrbit
