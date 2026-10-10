import Holant.Certificates.RainbowOrbit.SourceInterface
import Holant.Certificates.OppositeIcosahedral.Outputs
import Holant.Certificates.OppositeIcosahedral.PhysicalDictionary

/-! The opposite-I deck in the retained computational basis. Uniform D acts
only as an analytic dictionary here; actual current-group dressings are
constructed separately. -/
namespace Holant.Certificates.PlatonicIncidence.Opposite
open Holant Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
open Holant.Certificates.OppositeIcosahedral
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

abbrev BMat := Matrix Bool Bool ℂ

def legs : Legs := fun _ => D

theorem legs_det : ∀j,(legs j).det≠0 := fun _ => D_det_ne_zero

theorem transfer_iff (U : BMat) : Direction (U*OppositeIcosahedral.X) ↔ Direction U := by
  constructor
  · intro h
    have hh := Direction.mul h direction_X
    have hXX : OppositeIcosahedral.X*OppositeIcosahedral.X=(1 : BMat) := physicalX_square
    simpa only [mul_assoc,hXX,mul_one] using hh
  · exact fun h => Direction.mul h direction_X

theorem binaryTransport_mem_iff (U : BMat) :
    Direction (binaryTransport U) ↔ groupDirection .icosahedral U := by
  rw [←transfer_iff,output_transfer_iff]
  exact standard_source_transfer_iff .icosahedral U

theorem binaryTransport_kappa (U : BMat) : binaryTransport (kappa U)=U := by
  change D*kappa U*D.transpose=U
  rw [D_transpose]
  simpa only [unkappa,D_transpose] using unkappa_kappa U

theorem kappa_binaryTransport (U : BMat) : kappa (binaryTransport U)=U := by
  change kappa (D*U*D.transpose)=U
  rw [D_transpose]
  simpa only [unkappa,D_transpose] using kappa_unkappa U

theorem kappa_opposite_mem {U : BMat} (hU : Direction U) :
    groupDirection .icosahedral (kappa U) :=
  (binaryTransport_mem_iff (kappa U)).mp (by rwa [binaryTransport_kappa])

def InMatching (r : Fin 3) (F : FourTensor) : Prop := FamilyInMatching Direction r F

theorem matching_forward (r : Fin 3) (F : FourTensor)
    (hF : RainbowOrbit.InMatching .icosahedral r F) : InMatching r (act legs F) := by
  obtain ⟨U,V,hU,hV,rfl⟩ := hF
  refine ⟨binaryTransport U,binaryTransport V,
    (binaryTransport_mem_iff U).mpr hU,(binaryTransport_mem_iff V).mpr hV,?_⟩
  exact matching_label_preserved r U V

theorem matching_surjective (r : Fin 3) (F : FourTensor) (hF : InMatching r F) :
    ∃H,RainbowOrbit.InMatching .icosahedral r H ∧ act legs H=F := by
  obtain ⟨U,V,hU,hV,rfl⟩ := hF
  refine ⟨matchingTensor r (kappa U) (kappa V),
    ⟨_,_,kappa_opposite_mem hU,kappa_opposite_mem hV,rfl⟩,?_⟩
  change transport (matchingTensor r (kappa U) (kappa V))=matchingTensor r U V
  rw [matching_label_preserved,binaryTransport_kappa,binaryTransport_kappa]

theorem matching_iff (r : Fin 3) (F : FourTensor) :
    InMatching r (act legs F) ↔ RainbowOrbit.InMatching .icosahedral r F := by
  constructor
  · intro h
    obtain ⟨H,hH,he⟩ := matching_surjective r _ h
    have hh : H=F := actionLinear_injective legs legs_det he
    simpa only [hh] using hH
  · exact matching_forward r F

def point : Point→Point := pointAction legs legs_det

theorem point_injective : Function.Injective point := pointAction_injective _ _

def deck : Finset Point :=
  (RainbowOrbit.deck .icosahedral).map ⟨point,point_injective⟩

theorem deck_card : deck.card=10800 := by
  simp [deck,RainbowOrbit.deck_card,size]

def DeckPoint (p : Point) : Prop := FamilyDeckPoint Direction p

theorem deck_iff_mem (p : Point) : DeckPoint p ↔ p∈deck := by
  classical
  constructor
  · rintro ⟨r,F,hF,hM,rfl⟩
    obtain ⟨H,hH,he⟩ := matching_surjective r F hM
    have hH0 : H≠0 := by intro hz; apply hF; rw [←he,hz]; simp [act]
    have hm : Projectivization.mk ℂ H hH0∈RainbowOrbit.deck .icosahedral := by
      apply (inDeck_iff_mem .icosahedral H hH0).mp
      obtain ⟨U,V,hU,hV,rfl⟩ := hH
      exact ⟨r,U,V,hU,hV,Proportional.refl _⟩
    refine Finset.mem_map.mpr ⟨_,hm,?_⟩
    change Projectivization.mk ℂ (act legs H) _=Projectivization.mk ℂ F _
    congr 1
  · intro hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_map.mp hp
    induction q using Projectivization.ind with | h F hF =>
    obtain ⟨r,U,V,hU,hV,⟨c,hc,he⟩⟩ := (inDeck_iff_mem .icosahedral F hF).mpr hq
    have hmatch : RainbowOrbit.InMatching .icosahedral r F :=
      ⟨c • U,V,groupDirection_smul .icosahedral hU hc,hV,
        he.trans (matchingTensor_smul_left r c U V).symm⟩
    exact ⟨r,_,_,matching_forward r F hmatch,rfl⟩

end
end Holant.Certificates.PlatonicIncidence.Opposite
