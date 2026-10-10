import Holant.ReedMuller.RadonAccess.Quotient
import Mathlib.Data.Fintype.EquivFin

/-! The complement and orbit coordinates are the unchanged ordinary output
ports outside the recorded pair, with exactly `n-2` such ports. -/
namespace Holant.ReedMuller.RadonAccess
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n : ℕ}
namespace RadonFrame

@[simp] theorem dot_r_input (F : RadonFrame n) (x : BinaryVector n) :
    dot F.r x = F.A x F.i := by
  rw [←F.A.isometry,F.map_r,dot_unit_left]

@[simp] theorem dot_v_input (F : RadonFrame n) (x : BinaryVector n) :
    dot F.v x = F.A x F.i + F.A x F.j := by
  rw [←F.A.isometry,F.map_v,dot_add_left,dot_unit_left,dot_unit_left]

/-- The complement is precisely the coordinate complement of the two actual
selected output ports, after applying the recorded orthogonal map. -/
theorem complement_iff_output_zero (F : RadonFrame n) (x : BinaryVector n) :
    x ∈ F.complement ↔ F.A x F.i = 0 ∧ F.A x F.j = 0 := by
  rw [F.mem_complement,F.dot_r_input,F.dot_v_input]
  constructor
  · rintro ⟨hi,hij⟩
    exact ⟨hi,by simpa only [hi,zero_add] using hij⟩
  · rintro ⟨hi,hj⟩
    simp [hi,hj]

/-- Original port identities are retained by this subtype. -/
abbrev Remaining (F : RadonFrame n) := {k : Fin n // k ≠ F.i ∧ k ≠ F.j}

theorem remaining_card (F : RadonFrame n) : Fintype.card F.Remaining = n-2 := by
  rw [Fintype.card_subtype]
  have h : Finset.univ.filter (fun k : Fin n => k ≠ F.i ∧ k ≠ F.j) =
      ({F.i,F.j} : Finset (Fin n))ᶜ := by
    ext k
    simp
  rw [h,Finset.card_compl]
  simp [F.distinct]

/-- An optional ordinary `Fin (n-2)` order; the exact original-port map is
recorded by its inverse. -/
def remainingOrder (F : RadonFrame n) : F.Remaining ≃ Fin (n-2) :=
  Fintype.equivFinOfCardEq F.remaining_card

/-- Extend boundary coordinates by zero at the two removed ports. -/
def extendRemaining (F : RadonFrame n) (z : F.Remaining → ZMod 2) : BinaryVector n :=
  fun k => if h : k ≠ F.i ∧ k ≠ F.j then z ⟨k,h⟩ else 0

@[simp] theorem extendRemaining_i (F : RadonFrame n) (z : F.Remaining → ZMod 2) :
    F.extendRemaining z F.i = 0 := by simp [extendRemaining]
@[simp] theorem extendRemaining_j (F : RadonFrame n) (z : F.Remaining → ZMod 2) :
    F.extendRemaining z F.j = 0 := by simp [extendRemaining]
@[simp] theorem extendRemaining_remaining (F : RadonFrame n) (z : F.Remaining → ZMod 2)
    (k : F.Remaining) : F.extendRemaining z k.1 = z k := by simp [extendRemaining,k.property]

/-- Literal restriction of `A` to the surviving output ports. -/
def boundaryCoordinate (F : RadonFrame n) (w : F.complement) : F.Remaining → ZMod 2 :=
  fun k => F.A w k.1

def fromBoundary (F : RadonFrame n) (z : F.Remaining → ZMod 2) : F.complement :=
  ⟨F.A.symm (F.extendRemaining z), by
    rw [F.complement_iff_output_zero,F.A.apply_symm_apply]
    simp⟩

@[simp] theorem boundaryCoordinate_fromBoundary (F : RadonFrame n) (z : F.Remaining → ZMod 2) :
    F.boundaryCoordinate (F.fromBoundary z) = z := by
  funext k
  change F.A (F.A.symm (F.extendRemaining z)) k.1 = z k
  rw [F.A.apply_symm_apply,F.extendRemaining_remaining]

@[simp] theorem fromBoundary_boundaryCoordinate (F : RadonFrame n) (w : F.complement) :
    F.fromBoundary (F.boundaryCoordinate w) = w := by
  apply Subtype.ext
  apply F.A.linear.injective
  change F.A (F.A.symm (F.extendRemaining (F.boundaryCoordinate w))) = F.A w
  rw [F.A.apply_symm_apply]
  have hw := (F.complement_iff_output_zero w).mp w.property
  funext k
  by_cases hi : k = F.i
  · subst k; simpa using hw.1.symm
  · by_cases hj : k = F.j
    · subst k; simpa using hw.2.symm
    · simp [extendRemaining,hi,hj,boundaryCoordinate]

/-- A genuine linear coordinate equivalence on the remaining original ports. -/
def boundaryLinearEquiv (F : RadonFrame n) : F.complement ≃ₗ[ZMod 2]
    (F.Remaining → ZMod 2) where
  toFun := F.boundaryCoordinate
  invFun := F.fromBoundary
  left_inv := F.fromBoundary_boundaryCoordinate
  right_inv := F.boundaryCoordinate_fromBoundary
  map_add' := by intro x y; funext k; exact congrFun (F.A.map_add x y) k.1
  map_smul' := by intro c x; funext k; exact congrFun (F.A.map_smul c x) k.1

/-- The ordinary boundary dot product is exactly the inherited form on `W`. -/
theorem boundaryCoordinate_isometry (F : RadonFrame n) (w z : F.complement) :
    (∑ k : F.Remaining, F.boundaryCoordinate w k * F.boundaryCoordinate z k) =
      dot (w : BinaryVector n) z := by
  rw [←F.A.isometry]
  change (∑ k : {k : Fin n // k ≠ F.i ∧ k ≠ F.j},
    F.A w k.1 * F.A z k.1) = ∑ k : Fin n, F.A w k * F.A z k
  have hs := Finset.sum_subtype (F := inferInstance) (p := fun k : Fin n => k ≠ F.i ∧ k ≠ F.j)
    (Finset.univ.filter (fun k : Fin n => k ≠ F.i ∧ k ≠ F.j))
    (by intro k; simp) (fun k => F.A w k * F.A z k)
  rw [←hs,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : k ≠ F.i ∧ k ≠ F.j
  · simp [hk]
  · have hw := (F.complement_iff_output_zero w).mp w.property
    have he : k = F.i ∨ k = F.j := by tauto
    rcases he with rfl | rfl <;> simp [hk,hw.1,hw.2]

/-- A concrete ordinary `n-2` port coordinate map, with its original-port
incidence order retained by `remainingOrder.symm`. -/
def ordinaryBoundaryLinearEquiv (F : RadonFrame n) :
    F.complement ≃ₗ[ZMod 2] BinaryVector (n-2) :=
  F.boundaryLinearEquiv.trans
    (LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) F.remainingOrder.symm)

@[simp] theorem ordinaryBoundaryLinearEquiv_apply (F : RadonFrame n)
    (w : F.complement) (k : Fin (n-2)) :
    F.ordinaryBoundaryLinearEquiv w k = F.A w (F.remainingOrder.symm k).1 := rfl

theorem ordinaryBoundaryLinearEquiv_isometry (F : RadonFrame n) (w z : F.complement) :
    dot (F.ordinaryBoundaryLinearEquiv w) (F.ordinaryBoundaryLinearEquiv z) =
      dot (w : BinaryVector n) z := by
  change (∑ k : Fin (n-2), F.boundaryCoordinate w (F.remainingOrder.symm k) *
    F.boundaryCoordinate z (F.remainingOrder.symm k)) = _
  exact (Equiv.sum_comp F.remainingOrder.symm
    (fun k => F.boundaryCoordinate w k * F.boundaryCoordinate z k)).trans
      (F.boundaryCoordinate_isometry w z)

/-- Canonical orbit representatives keep all the surviving coordinates. -/
theorem quotientCoordinate_remaining (F : RadonFrame n) (ε : ZMod 2)
    (x : F.Hyperplane ε) (k : F.Remaining) :
    F.boundaryCoordinate (F.quotientCoordinate ε x) k = F.A x.1 k.1 := by
  simp only [boundaryCoordinate,quotientCoordinate,F.A.map_add,F.A.map_smul,
    F.map_r,F.map_v,Pi.add_apply,Pi.smul_apply,smul_eq_mul,unitWord_apply]
  simp [k.property.1,k.property.2]

/-- In the quotient's canonical lift, the first chosen port is `ε` and the
second is zero; every other coordinate is the recorded boundary coordinate. -/
theorem iota_output_coordinates (F : RadonFrame n) (ε : ZMod 2) (w : F.complement) :
    F.A (ε • F.r + w) F.i = ε ∧ F.A (ε • F.r + w) F.j = 0 ∧
      ∀ k : F.Remaining, F.A (ε • F.r + w) k.1 = F.boundaryCoordinate w k := by
  have hw := (F.complement_iff_output_zero w).mp w.property
  simp only [F.A.map_add,F.A.map_smul,F.map_r,Pi.add_apply,Pi.smul_apply,
    smul_eq_mul,unitWord_apply,ite_true,mul_one,hw.1,hw.2,add_zero]
  refine ⟨True.intro,?_,?_⟩
  · simp [Ne.symm F.distinct]
  · intro k
    simp [k.property.1,boundaryCoordinate]

end RadonFrame
end
end Holant.ReedMuller.RadonAccess
