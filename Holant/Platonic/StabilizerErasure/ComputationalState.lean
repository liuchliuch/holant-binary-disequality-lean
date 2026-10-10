import Holant.Platonic.StabilizerErasure.PureStabilizerResidual

/-! The computational unary factor in the pure normal form is itself a
genuine stabilizer state: it is the image of an actual zero-input encoder. -/
namespace Holant.Platonic.StabilizerErasure
open Holant Holant.Tractable.AffinePhase
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.AffinePatching Holant.ReedMuller.RadonAccess
open Holant.Platonic.StabilizerLine
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

def zeroInputCoordinates : BinaryVector 1 ≃ₗ[ZMod 2] BinaryVector 0 × BinaryVector 1 where
  toFun x := (0,x)
  invFun x := x.2
  left_inv _ := rfl
  right_inv x := Prod.ext (Subsingleton.elim _ _) rfl
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

def computationalStateEncoder (b : Bool) : StabilizerIsometry 0 1 :=
  ⟨1,zeroInputCoordinates,(resetBitProgram 0 b).clifford⟩

theorem computationalStateEncoder_map (b : Bool) :
    (computationalStateEncoder b).map=(auxiliaryKet b : Signature ℂ 0 →ₗ[ℂ] Signature ℂ 1) := by
  apply LinearMap.ext
  intro f
  funext w
  have hf (x : Word 0) : f x=f (origin 0) := congrArg f (Subsingleton.elim _ _)
  have hw : w=![w 0] := by ext j;fin_cases j;rfl
  rw [hw]
  cases b <;> cases hb : w 0 <;>
    simp [computationalStateEncoder,StabilizerIsometry.map,Program.clifford_apply,
      resetBitProgram,Program.run,attachZero,zeroInputCoordinates,translateAction,
      auxiliaryKet,wordVector,vectorWord,boolEquiv,hf,hb,unitWord_apply,
      funext_iff,Fin.forall_fin_succ]

theorem computationalState_stabilizer (b : Bool) :
    IsStabilizerIsometry (auxiliaryKet b : Signature ℂ 0 →ₗ[ℂ] Signature ℂ 1) := by
  rw [←computationalStateEncoder_map]
  exact (computationalStateEncoder b).semantic

end
end Holant.Platonic.StabilizerErasure
