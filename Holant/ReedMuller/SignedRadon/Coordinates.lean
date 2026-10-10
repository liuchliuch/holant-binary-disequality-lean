import Holant.ReedMuller.SignedRadon.Basic

/-! The boundary space consists of the literal remaining graph outputs,
including their native-input global complement. Its quotient map is an affine
isometry, with an explicit inverse and actual original incidence order. -/
namespace Holant.ReedMuller.SignedRadon
open Holant Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.RadonAccess Holant.ReedMuller.CharacterFlat
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

namespace RadonFrame

def boundaryAffine (F : RadonAccess.RadonFrame (n+2)) (d : ZMod 2) :
    F.Orbit d ≃ᵃ[ZMod 2] BinaryVector n :=
  (((F.quotientAffineEquiv d).symm).trans F.pairBoundaryLinearEquiv.toAffineEquiv).trans
    (AffineEquiv.vaddConst (ZMod 2) (ones n))

@[simp] theorem boundaryAffine_apply (F : RadonAccess.RadonFrame (n+2)) (d : ZMod 2)
    (q : F.Orbit d) :
    boundaryAffine F d q=F.pairBoundaryLinearEquiv (F.quotientToComplement d q)+ones n := rfl

@[simp] theorem boundaryAffine_linear (F : RadonAccess.RadonFrame (n+2)) (d : ZMod 2)
    (w : F.complement) : (boundaryAffine F d).linear w=F.pairBoundaryLinearEquiv w := rfl

theorem boundaryAffine_isometry (F : RadonAccess.RadonFrame (n+2)) (d : ZMod 2)
    (w z : F.complement) :
    dot ((boundaryAffine F d).linear w) ((boundaryAffine F d).linear z)=dot (w : BinaryVector (n+2)) z :=
  F.pairBoundaryLinearEquiv_isometry w z

@[simp] theorem boundaryAffine_symm (F : RadonAccess.RadonFrame (n+2)) (d : ZMod 2)
    (b : BinaryVector n) :
    (boundaryAffine F d).symm b=F.iota d (F.pairBoundaryLinearEquiv.symm (b+ones n)) := by
  apply (boundaryAffine F d).injective
  rw [AffineEquiv.apply_symm_apply,boundaryAffine_apply,F.quotientToComplement_iota,
    F.pairBoundaryLinearEquiv.apply_symm_apply,add_assoc,binary_add_self,add_zero]

theorem boundaryAffine_orbit (F : RadonAccess.RadonFrame (n+2)) (d : ZMod 2)
    (x : F.Hyperplane d) (k : Fin n) :
    boundaryAffine F d (F.orbit d x) k=F.A (x.1+ones (n+2)) (F.pairRemainingOrder k).1 := by
  rw [boundaryAffine_apply]
  change F.A (F.quotientCoordinate d x) (F.pairRemainingOrder k).1+1=_
  rw [F.A.map_add,F.A.fixes_ones]
  change F.A (x.1+d • F.r+(dot x.1 F.r+d) • F.v) (F.pairRemainingOrder k).1+1=_
  have hi := (F.pairRemainingOrder k).property.1
  have hj := (F.pairRemainingOrder k).property.2
  simp [F.A.map_add,F.A.map_smul,F.map_r,F.map_v,unitWord_apply,hi,hj,ones]

def boundaryCard (F : RadonAccess.RadonFrame (n+2)) (d l : ZMod 2)
    (g : Signature ℂ (n+2)) : Signature ℂ n := fun b =>
  signedCard F d l (fun x => g (wordVector x)) ((boundaryAffine F d).symm (vectorWord b))

def boundaryLift (F : RadonAccess.RadonFrame (n+2)) (d : ZMod 2)
    (b : BinaryVector n) : BinaryVector (n+2) :=
  d • F.r+F.pairBoundaryLinearEquiv.symm (b+ones n)

@[simp] theorem boundaryCard_apply (F : RadonAccess.RadonFrame (n+2)) (d l : ZMod 2)
    (g : Signature ℂ (n+2)) (b : Fin n → Bool) :
    boundaryCard F d l g b=sign (l*d)*
      (g (wordVector (boundaryLift F d (vectorWord b)))+
        sign l*g (wordVector (boundaryLift F d (vectorWord b)+F.v))) := by
  rw [boundaryCard,boundaryAffine_symm,signedCard_iota]
  rfl

end RadonFrame
end
end Holant.ReedMuller.SignedRadon
