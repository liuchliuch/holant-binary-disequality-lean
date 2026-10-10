import Holant.Complexity.BinaryInterpolation.AlgebraicSource.Pencil
import Holant.Complexity.BinaryInterpolation.Chains.DirectMacro

/-! The literal original-family macro is an algebraic representative of the
source's projectively realized binary. Its own macro scale is exactly one;
no algebraicity of an arbitrary projective representative is presumed. -/
namespace Holant.Complexity.BinaryInterpolation.AlgebraicSource
open Holant.Certificates.MatchingContractionClosure
open Holant.Projective.BoundedTorsion
open Holant.Tractable
open Holant.Complexity.FixedGadgetSubstitution
noncomputable section
set_option backward.isDefEq.respectTransparency false

 theorem network_algebraic {n : ℕ} (N : Network ℂ n)
    (hv : ∀v x, IsAlgebraic ℚ (N.vertex v x))
    (he : ∀e a b, IsAlgebraic ℚ (N.edge e a b)) (x : Fin n → Bool) :
    IsAlgebraic ℚ (N.denote x) := by
  apply IsIntegral.isAlgebraic
  unfold Network.denote
  apply IsIntegral.sum
  intro z _
  exact (IsIntegral.prod _ (fun v _ => (hv v _).isIntegral)).mul
    (IsIntegral.prod _ (fun e _ => (he e _ _).isIntegral))

variable {s : ℕ} {arity : ℕ → ℕ}
variable (G : (i : Fin s) → Signature ℂ (arity i.val))

structure Macro (B : Binary (K:=ℂ)) where
  scale : ℂ
  scale_nonzero : scale ≠ 0
  shape : NetworkShape 2
  label : Labelling shape s 1 arity
  binary : Binary (K:=ℂ)
  binary_eq : binary = scale • B
  denote_exact : (label.template.network label.wellFormed G
    (fun _ : Fin 1 => Signature.disequality)).denote = Chains.binarySignature binary
  binary_algebraic : EntriesAlgebraic binary
  determinant_nonzero : Matrix.det (binary*X) ≠ 0
  infinite_order : ¬ProjectivelyFinite (binary*X)

 theorem exists_macro (halg : ∀i x, IsAlgebraic ℚ (G i x))
    (B : Binary (K:=ℂ)) (hB : B≠0) (hd : Matrix.det (B*X)≠0)
    (hi : ¬ProjectivelyFinite (B*X))
    (hreal : Gadget.RealizesUpTo
      (Set.range (fun i => (⟨arity i.val,G i⟩ : AnySignature ℂ)))
      .disequality (Chains.binarySignature B)) : Nonempty (Macro G B) := by
  obtain ⟨c,hc,N,L,hL⟩ := Chains.original_labelled_macro arity G (0 : Fin 1)
    (fun _ => Signature.disequality) rfl B hB hi hreal
  let D : Binary (K:=ℂ) := c • B
  have hD : EntriesAlgebraic D := by
    intro a b
    have h := network_algebraic (L.template.network L.wellFormed G
      (fun _ : Fin 1 => Signature.disequality)) (by
        intro v x
        exact halg ⟨(L.template.vertices.get v).1,
          (L.wellFormed.1 _ (List.get_mem _ v)).1⟩ x)
      (fun e i j => entries_X i j) (![a,b] : Fin 2 → Bool)
    rw [hL] at h
    exact h
  have hiD : ¬ProjectivelyFinite (D*X) := by
    intro h
    apply hi
    have h' := h.smul (inv_ne_zero hc)
    simpa [D,Matrix.smul_mul,smul_smul,inv_mul_cancel₀ hc] using h'
  refine ⟨{
    scale := c, scale_nonzero := hc, shape := N.shape, label := L,
    binary := D, binary_eq := rfl, denote_exact := hL, binary_algebraic := hD,
    determinant_nonzero := ?_, infinite_order := hiD }⟩
  dsimp only [D]
  rw [Matrix.smul_mul,Matrix.det_smul]
  exact mul_ne_zero (pow_ne_zero _ hc) hd

namespace Macro
variable {G} {B : Binary (K:=ℂ)} (M : Macro G B)

/-- If the caller's representative is algebraic, its recorded macro scale is
algebraic too. The proof reads an actual nonzero binary entry. -/
theorem scale_algebraic (hB : B≠0) (hBa : EntriesAlgebraic B) : IsAlgebraic ℚ M.scale := by
  classical
  have hex : ∃ i j, B i j≠0 := by
    by_contra h
    push Not at h
    exact hB (by ext i j; exact h i j)
  obtain ⟨i,j,hij⟩ := hex
  have h : IsAlgebraic ℚ (M.binary i j / B i j) := by
    simpa only [div_eq_mul_inv] using (M.binary_algebraic i j).mul (hBa i j).inv
  rw [M.binary_eq] at h
  simpa only [Matrix.smul_apply,smul_eq_mul,mul_div_cancel_right₀ _ hij] using h

 theorem pencil_exists : Nonempty (Pencil M.binary) :=
  exists_pencil M.binary M.binary_algebraic M.determinant_nonzero M.infinite_order

end Macro
end
end Holant.Complexity.BinaryInterpolation.AlgebraicSource
