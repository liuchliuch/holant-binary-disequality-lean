import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeSparseMinimalRank
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeRankTwoPorts

/-! Rank-two minimality supplies full affine unary line factors from actual
proper original-port minors. No compressed line affinity is assumed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeRankTwoMinimalLines
open Holant Holant.Tractable Holant.Tractable.AffinePhase Holant.Tractable.TwoTranslate
open OrdinaryNegativeAffineSystematicSupport OrdinaryNegativeSparseRankDescent
namespace P
export OrdinaryNegativeRankTwoPorts (line port linePort original_line_word)
end P
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option Elab.async false

/-- Vary exactly one logical coordinate, with the other literally false. -/
def lineMap (axis : Fin 2) (z : Fin 1→Bool) : Fin 2→Bool := P.line axis (z 0)

theorem lineMap_affine (axis : Fin 2) : IsAffineMap (lineMap axis) := by
  intro x y
  funext i
  fin_cases axis <;> fin_cases i <;> simp [lineMap,P.line,AffinePhase.xor,origin]

theorem line_outside (axis : Fin 2) (b : Bool) (i : Fin 2) (hi : i∉({axis} : Finset (Fin 2))) :
    P.line axis b i=false := by
  fin_cases axis <;> fin_cases i <;> simp_all [P.line]

variable {n : ℕ} {f : Signature AlgebraicComplex n} (D : SystematicSupport f 2)
variable (minimal : ∀S : Finset (Fin 2),S.card<2→∀z : Fin 2→Bool,Affine (minor D S z))

include minimal in
/-- The unary factor is an affine pullback of the actual retained minor. -/
theorem line_affine (axis : Fin 2) :
    Affine (fun z : Fin 1→Bool=>f (D.encode (P.line axis (z 0)))) := by
  have hm := minimal {axis} (by simp) (fun _=>false)
  have hf := face_affine_of_minor D {axis} (fun _=>false) hm
  have hl := hf.precompose (lineMap axis) (lineMap_affine axis)
  convert hl using 1
  funext z
  change f (D.encode (P.line axis (z 0)))=
    if ∀i,i∉({axis} : Finset (Fin 2))→lineMap axis z i=false then f (D.encode (lineMap axis z)) else 0
  simp only [lineMap]
  rw [ite_eq_left (fun i hi=>line_outside axis (z 0) i hi)]

theorem line_full (axis : Fin 2) (z : Fin 1→Bool) :
    f (D.encode (P.line axis (z 0)))≠0 := D.supported _

include minimal in
theorem first_affine : Affine (fun z : Fin 1→Bool=>f (D.encode ![z 0,false])) := by
  simpa only [P.line,ite_true] using line_affine D minimal 0

include minimal in
theorem second_affine : Affine (fun z : Fin 1→Bool=>f (D.encode ![false,z 0])) := by
  simpa only [P.line,show (1 : Fin 2)≠0 by decide,ite_false] using line_affine D minimal 1

theorem first_full (z : Fin 1→Bool) : f (D.encode ![z 0,false])≠0 := D.supported _
theorem second_full (z : Fin 1→Bool) : f (D.encode ![false,z 0])≠0 := D.supported _

include minimal in
/-- The literal signed-port line used by the mixing gadget inherits this
proved affine unary through an actual coordinate projection. -/
theorem physical_line_affine (axis : Fin 2) (target : Fin 3) :
    Affine (fun z=>f (OrdinaryNegativeSignedPortsCore.word (P.linePort (P.port D) axis target) z)) := by
  have hm : IsAffineMap (fun z : Fin 3→Bool=>fun _ : Fin 1=>z target) := by
    intro x y
    funext i
    simp [AffinePhase.xor,origin]
  convert (line_affine D minimal axis).precompose (fun z : Fin 3→Bool=>fun _ : Fin 1=>z target) hm using 1
  funext z
  rw [P.original_line_word]

theorem physical_line_full (axis : Fin 2) (target : Fin 3) (z : Fin 3→Bool) :
    f (OrdinaryNegativeSignedPortsCore.word (P.linePort (P.port D) axis target) z)≠0 := by
  rw [P.original_line_word]
  exact D.supported _

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeRankTwoMinimalLines
end
