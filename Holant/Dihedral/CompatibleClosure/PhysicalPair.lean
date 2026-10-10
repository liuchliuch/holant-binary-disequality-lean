import Holant.Dihedral.CompatibleClosure.ActualClosure
import Holant.Dihedral.CompatibleClosure.OriginalOrder
import Holant.Dihedral.CompatibleClosure.Prepared

/-! Two actual products share one original contraction order and one actual
phase representative. Their possible circle scalars are individually recorded. -/
noncomputable section
namespace Holant.Dihedral.CompatibleClosure
open Holant Holant.Marked

structure PhysicalPair {m n : ℕ} (F : SignatureFamily Scalar) (G : ActualRepresentatives F m)
    (q₀ q₁ : Signature Scalar (n+2)) (order : Equiv.Perm (Fin (n+2)))
    (γ : Bool) (t : {t : Scalar // Roots m t}) where
  circle₀ : Scalar
  circle₁ : Scalar
  circle₀_choice : circle₀ = 1 ∨ circle₀ = (2:Scalar)⁻¹
  circle₁_choice : circle₁ = 1 ∨ circle₁ = (2:Scalar)⁻¹
  multiplier₀_nonzero : circle₀ * G.multiplier γ t ≠ 0
  multiplier₁_nonzero : circle₁ * G.multiplier γ t ≠ 0
  actual₀ : Gadget.Realizes F .disequality
    ((circle₀*G.multiplier γ t) • close γ t.val (Tensor.reindex order.symm q₀))
  actual₁ : Gadget.Realizes F .disequality
    ((circle₁*G.multiplier γ t) • close γ t.val (Tensor.reindex order.symm q₁))
  nonzero₀ : (circle₀*G.multiplier γ t) • close γ t.val (Tensor.reindex order.symm q₀) ≠ 0
  nonzero₁ : (circle₁*G.multiplier γ t) • close γ t.val (Tensor.reindex order.symm q₁) ≠ 0

/-- The actual coefficient sum is used, with no gadget assumption on its
analytic factors. -/
theorem physical_pair {m n : ℕ} (F : SignatureFamily Scalar) (G : ActualRepresentatives F m)
    (q₀ q₁ : Signature Scalar (n+2)) (order : Equiv.Perm (Fin (n+2)))
    (hq₀ : Gadget.Realizes F .disequality q₀) (hq₁ : Gadget.Realizes F .disequality q₁)
    (γ : Bool) (t : {t : Scalar // Roots m t})
    (h₀ : close γ t.val (Tensor.reindex order.symm q₀) ≠ 0)
    (h₁ : close γ t.val (Tensor.reindex order.symm q₁) ≠ 0) :
    Nonempty (PhysicalPair F G q₀ q₁ order γ t) := by
  obtain ⟨c₀,he₀,hc₀,hm₀,hr₀⟩ := actual_phase_connection F G q₀ hq₀ order γ t
  obtain ⟨c₁,he₁,hc₁,hm₁,hr₁⟩ := actual_phase_connection F G q₁ hq₁ order γ t
  exact ⟨⟨c₀,c₁,he₀,he₁,hm₀,hm₁,hr₀,hr₁,scalar_tensor_nonzero hm₀ h₀,
    scalar_tensor_nonzero hm₁ h₁⟩⟩

/-- Every protected outside determinant retains its exact nonzero multiplier,
including both original representative factors and both possible circle factors. -/
theorem PhysicalPair.protected {m n : ℕ} {F : SignatureFamily Scalar} {G : ActualRepresentatives F m}
    {q₀ q₁ : Signature Scalar (n+2)} {order : Equiv.Perm (Fin (n+2))}
    {γ : Bool} {t : {t : Scalar // Roots m t}} (P : PhysicalPair F G q₀ q₁ order γ t)
    (a₀ b₀ a₁ b₁ : Scalar) (h : a₀*b₁-b₀*a₁ ≠ 0) :
    ((P.circle₀*G.multiplier γ t)*a₀)*((P.circle₁*G.multiplier γ t)*b₁) -
      ((P.circle₀*G.multiplier γ t)*b₀)*((P.circle₁*G.multiplier γ t)*a₁) =
      ((P.circle₀*G.multiplier γ t)*(P.circle₁*G.multiplier γ t))*(a₀*b₁-b₀*a₁) ∧
    ((P.circle₀*G.multiplier γ t)*a₀)*((P.circle₁*G.multiplier γ t)*b₁) -
      ((P.circle₀*G.multiplier γ t)*b₀)*((P.circle₁*G.multiplier γ t)*a₁) ≠ 0 :=
  protected_outside_tag P.multiplier₀_nonzero P.multiplier₁_nonzero h

end Holant.Dihedral.CompatibleClosure
