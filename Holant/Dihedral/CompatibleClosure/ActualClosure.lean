import Holant.Dihedral.CompatibleClosure.SpliceSum
import Holant.Dihedral.CompatibleClosure.ActualReindex
import Holant.Dihedral.CompatibleClosure.Contractions
import Holant.OpenNetworkComposition.ProjectiveContraction

/-! Arbitrary actual gadgets can be connected by two native-X wires, with
an explicit invertible factor for a deleted wire-only circle. All original
representative and circle scalars are retained separately. -/
noncomputable section
namespace Holant.Dihedral.CompatibleClosure
open Holant Holant.Marked Holant.Tractable Holant.OpenNetworkComposition

/-- Actual q and actual C over the same family suffice. A possible circle is
handled by the proved factor2 rule, never by unrestricted exact self-gluing. -/
theorem realizes_native_connection {n : ℕ} (F : SignatureFamily Scalar)
    (q : Signature Scalar (n+2)) (C : Mat)
    (hq : Gadget.Realizes F .disequality q)
    (hc : Gadget.Realizes F .disequality (kernelSignature C)) :
    ∃ c : Scalar, (c = 1 ∨ c = (2:Scalar)⁻¹) ∧ c ≠ 0 ∧
      Gadget.Realizes F .disequality (fun x => c * nativeCardValue q C x) := by
  obtain ⟨c,he,hc0,hreal⟩ := realizes_contract_with_scale F
    (spliceTensor q (kernelSignature C) 1) (realizes_first_connection F q C hq hc) (by norm_num : (2:Scalar) ≠ 0)
  exact ⟨c,he,hc0,by simpa only [contract_splice_eq_nativeCard] using hreal⟩

theorem realizes_native_connection_ordered {n : ℕ} (F : SignatureFamily Scalar)
    (q : Signature Scalar (n+2)) (C : Mat) (order : Equiv.Perm (Fin (n+2)))
    (hq : Gadget.Realizes F .disequality q)
    (hc : Gadget.Realizes F .disequality (kernelSignature C)) :
    ∃ c : Scalar, (c = 1 ∨ c = (2:Scalar)⁻¹) ∧ c ≠ 0 ∧
      Gadget.Realizes F .disequality (fun x => c * nativeCardValue (Tensor.reindex order.symm q) C x) :=
  realizes_native_connection F _ C (realizes_reindex F .disequality q hq order) hc

/-- These are genuine actual group representatives, with their fixed exact
normalization coefficients. Analytic monomial factors are not resources. -/
structure ActualRepresentatives (F : SignatureFamily Scalar) (m : ℕ) where
  binary : Bool → {t : Scalar // Roots m t} → Mat
  multiplier : Bool → {t : Scalar // Roots m t} → Scalar
  multiplier_ne_zero : ∀ γ t, multiplier γ t ≠ 0
  actual : ∀ γ t, Gadget.Realizes F .disequality (kernelSignature (binary γ t))
  normalization : ∀ γ t, binary γ t = scale (multiplier γ t) (connection γ t.val)

/-- The final actual coefficient multiplier is the original representative
scalar times an explicitly known nonzero circle factor. -/
theorem actual_phase_connection {m n : ℕ} (F : SignatureFamily Scalar)
    (G : ActualRepresentatives F m) (q : Signature Scalar (n+2))
    (hq : Gadget.Realizes F .disequality q) (order : Equiv.Perm (Fin (n+2)))
    (γ : Bool) (t : {t : Scalar // Roots m t}) :
    ∃ c : Scalar, (c = 1 ∨ c = (2:Scalar)⁻¹) ∧ c ≠ 0 ∧ c*G.multiplier γ t ≠ 0 ∧
      Gadget.Realizes F .disequality
        ((c*G.multiplier γ t) • close γ t.val (Tensor.reindex order.symm q)) := by
  obtain ⟨c,he,hc,hreal⟩ := realizes_native_connection_ordered F q (G.binary γ t) order hq (G.actual γ t)
  refine ⟨c,he,hc,mul_ne_zero hc (G.multiplier_ne_zero γ t),?_⟩
  rw [G.normalization,actual_close] at hreal
  convert hreal using 1
  funext x
  simp only [Pi.smul_apply,smul_eq_mul,mul_assoc]

end Holant.Dihedral.CompatibleClosure
