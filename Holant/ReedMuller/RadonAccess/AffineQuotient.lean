import Holant.ReedMuller.RadonAccess.Quotient
import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv

/-! The orbit set is an actual affine space.  The transported action is
verified against addition of the original hyperplane representatives. -/
namespace Holant.ReedMuller.RadonAccess
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}
namespace RadonFrame

instance orbitNonempty (F : RadonFrame n) (ε : ZMod 2) : Nonempty (F.Orbit ε) :=
  ⟨F.iota ε 0⟩

instance orbitTorsor (F : RadonFrame n) (ε : ZMod 2) : AddTorsor F.complement (F.Orbit ε) where
  vadd w q := F.iota ε (w + F.quotientToComplement ε q)
  zero_vadd := by
    intro q
    change F.iota ε (0+F.quotientToComplement ε q) = q
    rw [zero_add,F.iota_quotientToComplement]
  add_vadd := by
    intro u w q
    change F.iota ε ((u+w)+F.quotientToComplement ε q) =
      F.iota ε (u+F.quotientToComplement ε (F.iota ε (w+F.quotientToComplement ε q)))
    rw [F.quotientToComplement_iota,add_assoc]
  vsub q q' := F.quotientToComplement ε q - F.quotientToComplement ε q'
  nonempty := ⟨F.iota ε 0⟩
  vsub_vadd' := by
    intro q q'
    change F.iota ε ((F.quotientToComplement ε q-F.quotientToComplement ε q')+
      F.quotientToComplement ε q') = q
    rw [sub_add_cancel,F.iota_quotientToComplement]
  vadd_vsub' := by
    intro w q
    change F.quotientToComplement ε (F.iota ε (w+F.quotientToComplement ε q))-
      F.quotientToComplement ε q = w
    rw [F.quotientToComplement_iota,add_sub_cancel_right]

/-- The source map is a genuine affine equivalence; its linear part is the
isometric identification of `W` with the translation quotient. -/
def quotientAffineEquiv (F : RadonFrame n) (ε : ZMod 2) :
    F.complement ≃ᵃ[ZMod 2] F.Orbit ε where
  toEquiv := F.quotientEquiv ε
  linear := LinearEquiv.refl _ _
  map_vadd' := by
    intro p w
    change F.iota ε (w+p) = F.iota ε (w+F.quotientToComplement ε (F.iota ε p))
    rw [F.quotientToComplement_iota]

/-- The coordinate construction commutes with actual translations by `W`. -/
theorem quotientCoordinate_add_complement (F : RadonFrame n) (ε : ZMod 2)
    (x y : F.Hyperplane ε) (w : F.complement) (hy : y.1 = x.1 + w) :
    F.quotientCoordinate ε y = F.quotientCoordinate ε x + w := by
  apply Subtype.ext
  have hw : dot (w : BinaryVector n) F.r = 0 := by rw [dot_comm]; exact w.property.1
  change y.1 + ε • F.r + (dot y.1 F.r + ε) • F.v =
    (x.1 + ε • F.r + (dot x.1 F.r + ε) • F.v) + w
  rw [hy,dot_add_left,hw,add_zero]
  abel

/-- The affine action is the genuine representative action `[x]↦[x+w]`. -/
theorem vadd_orbit (F : RadonFrame n) (ε : ZMod 2)
    (x y : F.Hyperplane ε) (w : F.complement) (hy : y.1 = x.1 + w) :
    w +ᵥ F.orbit ε x = F.orbit ε y := by
  apply (F.quotientEquiv ε).symm.injective
  change F.quotientToComplement ε (F.iota ε (w+F.quotientCoordinate ε x)) =
    F.quotientCoordinate ε y
  rw [F.quotientToComplement_iota,F.quotientCoordinate_add_complement ε x y w hy,add_comm]

/-- The induced symmetric form on the literal translation quotient is
nondegenerate, as well as representative-independent. -/
theorem quotientDot_nondegenerate (F : RadonFrame n) (q : F.Orbit 0)
    (hq : ∀ z : F.Orbit 0, F.quotientDot q z = 0) : q = F.iota 0 0 := by
  apply (F.quotientEquiv 0).symm.injective
  change F.quotientToComplement 0 q = F.quotientToComplement 0 (F.iota 0 0)
  rw [F.quotientToComplement_iota]
  apply Subtype.ext
  apply F.complement_nondegenerate
  intro w
  have h := hq (F.iota 0 w)
  simpa only [quotientDot,quotientToComplement_iota] using h

theorem quotientDot_symmetric (F : RadonFrame n) (q z : F.Orbit 0) :
    F.quotientDot q z = F.quotientDot z q := dot_comm _ _

/-- Actual Radon values descend to the two-point quotient. -/
def radon (F : RadonFrame n) (ε : ZMod 2) (g : BinaryVector n → ℂ) : F.Orbit ε → ℂ :=
  Quotient.lift (fun x : F.Hyperplane ε => g x.1 + g (x.1+F.v)) (by
    intro x y h
    rcases h with h | h
    · simp only [h]
    · rw [h,add_assoc,binary_add_self,add_zero,add_comm])

@[simp] theorem radon_orbit (F : RadonFrame n) (ε : ZMod 2) (g : BinaryVector n → ℂ)
    (x : F.Hyperplane ε) : F.radon ε g (F.orbit ε x) = g x.1 + g (x.1+F.v) := rfl

/-- The affine isometry uses exactly the two original-coordinate lifts
specified in the source, with no choice-dependent evaluation. -/
@[simp] theorem radon_iota (F : RadonFrame n) (ε : ZMod 2) (g : BinaryVector n → ℂ)
    (w : F.complement) : F.radon ε g (F.iota ε w) =
      g (ε • F.r + w) + g (ε • F.r + w + F.v) := rfl

end RadonFrame
end
end Holant.ReedMuller.RadonAccess
