import Holant.Platonic.RankDeficientLocalization.Normalization.MarkedCards

/-! The first clause of A.24 in the literal original domain coordinates.
The whole projective line avoids the kernel, beyond its three finite points. -/
namespace Holant.Platonic.RankDeficientLocalization.Normalization
open Holant Holant.Certificates Holant.Certificates.MatchingProductBridge
open Holant.Certificates.RainbowOrbit Holant.Certificates.PlatonicIncidence
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem standard_rainbow (g : PlatonicModel) (Φ : Mat →ₗ[ℂ] FourTensor)
    (hc : ∀i,matchingCone g (Φ (representative g i))) (hm : MixedCards Φ (representative g)) :
    Nonempty (RainbowDomainLine Φ (representative g)) :=
  platonic_mixed_rainbow g (LinearEquiv.refl ℂ Mat) Φ (fun i => matchingCone_card g _ (hc i)) hm

theorem marked_rainbow (f : Form) (Φ : Mat →ₗ[ℂ] FourTensor)
    (hc : ∀i,MarkedCone f (Φ (markedRepresentative f i))) (hm : MixedCards Φ (markedRepresentative f)) :
    Nonempty (RainbowDomainLine Φ (markedRepresentative f)) := by
  have he : (fun i : Fin 24 => thetaEquiv f (representative .octahedral i))=markedRepresentative f :=
    funext (theta_representative f)
  have hcards : ∀i,Φ (thetaEquiv f (representative .octahedral i))=0 ∨
      Nonempty (NonsingularCard (Φ (thetaEquiv f (representative .octahedral i)))) := by
    intro i
    rw [theta_representative]
    exact markedCone_card f _ (hc i)
  have hmix : MixedCards Φ (fun i => thetaEquiv f (representative .octahedral i)) := by
    exact he.symm ▸ hm
  have h := platonic_mixed_rainbow .octahedral (thetaEquiv f) Φ hcards hmix
  exact he ▸ h

end
end Holant.Platonic.RankDeficientLocalization.Normalization
