import Holant.Dihedral.CompatibleClosure.ActualClosure

/-! Construct the source connection representatives from the fixed actual
transfer representatives B_g X = kappa_g T_g. The physical connection identity
is proved, rather than supplied as a new normalization hypothesis. -/
noncomputable section
namespace Holant.Dihedral.CompatibleClosure
open Holant Holant.Marked Holant.Tractable

structure TransferRepresentatives (F : SignatureFamily Scalar) (m : ℕ) where
  binary : Bool → {t : Scalar // Roots m t} → Mat
  multiplier : Bool → {t : Scalar // Roots m t} → Scalar
  multiplier_ne_zero : ∀ γ t, multiplier γ t ≠ 0
  actual : ∀ γ t, Gadget.Realizes F .disequality (kernelSignature (binary γ t))
  transfer : ∀ γ t, Kernel.mul (binary γ t) Signature.disequality =
    scale (multiplier γ t) (if γ then S t.val else R t.val)

def inversePhase {m : ℕ} (t : {t : Scalar // Roots m t}) : {t : Scalar // Roots m t} :=
  ⟨t.val⁻¹,t.property.inv⟩

private theorem representative_entry {F : SignatureFamily Scalar} {m : ℕ}
    (G : TransferRepresentatives F m) (γ : Bool) (t : {t : Scalar // Roots m t}) (a b : Bool) :
    G.binary γ t a b = G.multiplier γ t * (if γ then S t.val else R t.val) a (!b) := by
  have hh := congrFun (congrFun (G.transfer γ t) a) (!b)
  simpa only [Kernel.mul_disequality,Bool.not_not,scale] using hh

/-- The off-diagonal source orientation reverses the phase and contributes
exactly the recorded factor 1/t, which is nonzero on the finite grid. -/
def TransferRepresentatives.connections {F : SignatureFamily Scalar} {m : ℕ}
    (G : TransferRepresentatives F m) (hm : 0 < m) : ActualRepresentatives F m where
  binary γ t := if γ then G.binary false (inversePhase t) else G.binary true t
  multiplier γ t := if γ then G.multiplier false (inversePhase t) / t.val else G.multiplier true t
  multiplier_ne_zero := by
    intro γ t
    cases γ
    · exact G.multiplier_ne_zero true t
    · exact div_ne_zero (G.multiplier_ne_zero false (inversePhase t)) (t.property.ne_zero hm)
  actual := by
    intro γ t
    cases γ
    · exact G.actual true t
    · exact G.actual false (inversePhase t)
  normalization := by
    intro γ t
    have ht := t.property.ne_zero hm
    funext a b
    cases γ <;> cases a <;> cases b <;>
      simp [representative_entry,connection,Kernel.mul_apply,Signature.disequality,
        R,S,diagonalKernel,M,monomial,scale,inversePhase] <;> field_simp

end Holant.Dihedral.CompatibleClosure
