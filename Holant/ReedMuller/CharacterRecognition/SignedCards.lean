import Holant.ReedMuller.SignedRadon.Basic
import Holant.ReedMuller.AffineRadon.NoCancellation

/-! Both signed cards on the same genuine Radon quotient and the same ordinary
boundary coordinates as `actualRadon`. No support conclusion is assumed. -/
noncomputable section
namespace Holant.ReedMuller.CharacterRecognition.SignedTransport
open Holant Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.CharacterFlat Holant.ReedMuller.RadonAccess
variable {n : ℕ}

 def actualSignedRadon (F : RadonAccess.RadonFrame n) (d l : ZMod 2)
    (g : BinaryVector n → ℂ) : BinaryVector (n-2) → ℂ := fun x =>
  SignedRadon.RadonFrame.signedCard F d l g
    (F.iota d (F.boundaryLinearEquiv.symm (fun k => x (F.remainingOrder k))))

 theorem actualSignedRadon_apply (F : RadonAccess.RadonFrame n) (d l : ZMod 2)
    (g : BinaryVector n → ℂ) (x : BinaryVector (n-2)) :
    actualSignedRadon F d l g x=sign (l*d)*
      (g (AffineRadon.RadonFrame.boundaryLift F d x)+
        sign l*g (AffineRadon.RadonFrame.boundaryLift F d x+F.v)) := by
  rw [actualSignedRadon,SignedRadon.RadonFrame.signedCard_iota]
  rfl

 theorem actualSignedRadon_nonzero_iff (F : RadonAccess.RadonFrame n) (d l : ZMod 2)
    (g : BinaryVector n → ℂ) (x : BinaryVector (n-2)) :
    actualSignedRadon F d l g x≠0 ↔
      g (AffineRadon.RadonFrame.boundaryLift F d x)+
        sign l*g (AffineRadon.RadonFrame.boundaryLift F d x+F.v)≠0 := by
  rw [actualSignedRadon_apply,mul_ne_zero_iff]
  exact and_iff_right (sign_nonzero _)

 theorem actualSignedRadon_plus (F : RadonAccess.RadonFrame n) (d : ZMod 2)
    (g : BinaryVector n → ℂ) : actualSignedRadon F d 0 g=AffineRadon.RadonFrame.actualRadon F d g := by
  funext x
  simp [actualSignedRadon_apply,AffineRadon.RadonFrame.actualRadon]


 theorem actualSignedRadon_projection (F : RadonAccess.RadonFrame n) (d l : ZMod 2)
    (g : BinaryVector n → ℂ) (x : BinaryVector n) (hx : dot x F.v=d) :
    actualSignedRadon F d l g (AffineRadon.RadonFrame.boundaryProjection F x)=
      sign (l*SignedRadon.RadonFrame.selected F x)*(g x+sign l*g (x+F.v)) := by
  have hh := (AffineRadon.RadonFrame.boundary_fiber F d
    (AffineRadon.RadonFrame.boundaryProjection F x) x hx).mp rfl
  change SignedRadon.RadonFrame.signedValue F l g
    (AffineRadon.RadonFrame.boundaryLift F d (AffineRadon.RadonFrame.boundaryProjection F x))=
      SignedRadon.RadonFrame.signedValue F l g x
  rcases hh with hh | hh
  · conv_rhs => rw [hh]
  · conv_rhs => rw [hh,SignedRadon.RadonFrame.signedValue_translate]

end Holant.ReedMuller.CharacterRecognition.SignedTransport
