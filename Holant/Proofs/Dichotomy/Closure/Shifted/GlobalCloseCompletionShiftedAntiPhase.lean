import Holant.Proofs.Dichotomy.Closure.Shifted.GlobalCloseCompletionShiftedMarking
import Holant.Marked.SupportAtlas.Source

/-! Two actual shifted phase slots suffice for the eighth-power obstruction:
if their anti ratios are eighth roots, the rotation order is exactly four.
No minimal-order assertion about the independently selected reflection is used. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxRecDepth 32768
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionShiftedAntiPhase
open Holant Holant.Tractable Holant.Marked Holant.Marked.SupportAtlas
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.Projective.BoundedTorsion
open Holant.LocalDrafts.RemoteWork.StableClosureV2
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (native : GlobalCloseCompletionShiftedMarking.Native G P torsion)

abbrev selected := native.reflection.selected native.axis native.notTwo native.notFour

def primitivePhase : Phase (selected G P torsion native).m :=
  ⟨ClosureMarkedDihedral.liftRoot (by have := (selected G P torsion native).range; omega)
    (selected G P torsion native).omega (selected G P torsion native).primitive,
    ClosureMarkedDihedral.liftRoot_root (by have := (selected G P torsion native).range; omega)
      (selected G P torsion native).omega (selected G P torsion native).primitive⟩

theorem two_ratios_force_four
    (first : (-native.reflection.eta)^8=1)
    (second : (-native.reflection.eta*(primitivePhase G P torsion native).val)^8=1) :
    (selected G P torsion native).m=4 := by
  have eta8 : native.reflection.eta^8=1 := by
    simpa only [show (-native.reflection.eta)^8=native.reflection.eta^8 from by ring] using first
  have phase8 : (primitivePhase G P torsion native).val^8=1 := by
    rw [mul_pow,first,one_mul] at second
    exact second
  have unitRoot : (selected G P torsion native).omega^8=1 := by
    apply Units.ext
    change ((selected G P torsion native).omega : ℂ)^8=1
    exact congrArg (fun z : Scalar=>(z : ℂ)) phase8
  have divides := (selected G P torsion native).primitive.dvd_of_pow_eq_one 8 unitRoot
  have upper : (selected G P torsion native).m≤8 := Nat.le_of_dvd (by decide) divides
  have lower : 4≤(selected G P torsion native).m :=
    native.reflection.selected_range P.equality native.axis native.notTwo native.notFour
  have notEight : (selected G P torsion native).m≠8 := by
    intro eight
    apply native.reflection.eta_not_root native.axis native.notTwo native.notFour native.noZ
    change native.reflection.eta^(selected G P torsion native).m=1
    rw [eight]
    exact eta8
  have choices : (selected G P torsion native).m=4 ∨ (selected G P torsion native).m=5 ∨
      (selected G P torsion native).m=6 ∨ (selected G P torsion native).m=7 := by omega
  rcases choices with four|five|six|seven
  · exact four
  · rw [five] at divides; norm_num at divides
  · rw [six] at divides; norm_num at divides
  · rw [seven] at divides; norm_num at divides

theorem outside_four_eighth_failure (notFour : (selected G P torsion native).m≠4) :
    (-native.reflection.eta)^8≠1 ∨
      (-native.reflection.eta*(primitivePhase G P torsion native).val)^8≠1 := by
  by_cases first : (-native.reflection.eta)^8=1
  · exact Or.inr (fun second=>notFour (two_ratios_force_four G P torsion native first second))
  · exact Or.inl first

theorem eta_fourth_eq_neg_one (four : (selected G P torsion native).m=4) :
    native.reflection.eta^4= -1 := by
  have root : native.reflection.eta^8=1 := by
    simpa only [Roots,four,show 2*4=8 from rfl] using
      native.reflection.eta_root native.axis native.notTwo native.notFour
  have notRoot : native.reflection.eta^4≠1 := by
    simpa only [Roots,four] using
      native.reflection.eta_not_root native.axis native.notTwo native.notFour native.noZ
  have factor : (native.reflection.eta^4-1)*(native.reflection.eta^4+1)=0 := by
    calc
      _=native.reflection.eta^8-1 := by ring
      _=0 := by rw [root]; ring
  rcases mul_eq_zero.mp factor with first|second
  · exact (notRoot (sub_eq_zero.mp first)).elim
  · linear_combination second

theorem order_four_ratio_fourth (four : (selected G P torsion native).m=4)
    (t : Phase (selected G P torsion native).m) : (-native.reflection.eta*t.val)^4= -1 := by
  have ht : t.val^4=1 := by simpa only [Roots,four] using t.property
  rw [mul_pow,show (-native.reflection.eta)^4=native.reflection.eta^4 from by ring,
    eta_fourth_eq_neg_one G P torsion native four,ht,mul_one]


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionShiftedAntiPhase
end
