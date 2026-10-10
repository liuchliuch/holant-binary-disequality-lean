import Holant.Dihedral.TwoCardLocalization.TaggedReduction
import Holant.Dihedral.TwoCardLocalization.ProgramMap

/-! Both mathematical localization branches use one common actual ancestor
program, preserve only the two chosen cards, and use exactly (arity-6)/2
fixed actual group representatives. The terminal non-product obstruction is
proved separately from this construction. -/
noncomputable section
namespace Holant.Dihedral.TwoCardLocalization
open Holant Holant.Marked Holant.Dihedral.CompatibleClosure Holant.Certificates
set_option backward.isDefEq.respectTransparency false

def Disagreement (m n : ℕ) (q₀ q₁ : Signature Scalar n) : Prop :=
  DifferentProducts (groupM m) n q₀ q₁ ∨ TwoTags m n q₀ q₁

theorem Disagreement.scale {m n : ℕ} {q₀ q₁ : Signature Scalar n} (h : Disagreement m n q₀ q₁)
    (c : Scalar) (hc : c ≠ 0) : Disagreement m n (c • q₀) (c • q₁) := by
  rcases h with h|h
  · exact Or.inl (h.scale c hc)
  · exact Or.inr (h.scale c hc)

theorem Disagreement.nonzero {m n : ℕ} (hm : 0<m) {q₀ q₁ : Signature Scalar n}
    (h : Disagreement m n q₀ q₁) : q₀ ≠ 0 ∧ q₁ ≠ 0 := by
  rcases h with h|h
  · exact h.nonzero (groupM_matrix_group hm)
  · exact h.nonzero hm

theorem localization_program {m : ℕ} (hm : 3 ≤ m) (r : ℕ)
    (q₀ q₁ : Signature Scalar (2*r+4)) (h : Disagreement m _ q₀ q₁) :
    ∃ P : Program (PhaseLabel m) (2*r+4) 4, P.length=r ∧
      Disagreement m 4 (P.residual phaseKernel q₀) (P.residual phaseKernel q₁) := by
  rcases h with h|h
  · obtain ⟨P,hP,hout⟩ := different_products_program (groupM m) (groupM_matrix_group (by omega))
      (groupM_X (by omega)) (groupM_reversal (by omega)) (M false 1)
      ((safe_groupM_iff (by omega) _).mpr (M_mem_group (by omega) false (Roots.one m))) r q₀ q₁ h
    let label : PhaseLabel m := (false,⟨1,Roots.one m⟩)
    refine ⟨P.map (fun _ => label),by simpa using hP,Or.inl ?_⟩
    simpa only [Program.map_residual,phaseKernel,label] using hout
  · obtain ⟨P,hP,hout⟩ := two_tags_program hm r q₀ q₁ h
    exact ⟨P,hP,Or.inr hout⟩

/-- A concrete source six-port output. Its exact common program, nonzero
physical scalar and linear representative count are retained in the witness. -/
theorem actual_localization {m : ℕ} (hm : 3 ≤ m)
    (F : SignatureFamily Scalar) (G : TransferRepresentatives F m)
    (r : ℕ) (f : Signature Scalar (2*r+6)) (hf : Gadget.Realizes F .disequality f)
    (A₀ A₁ : Mat) (h : Disagreement m (2*r+4) (Signature.contract A₀ f) (Signature.contract A₁ f)) :
    ∃ P : Program (PhaseLabel m) (2*r+4) 4, ∃ c : Scalar,c ≠ 0 ∧ P.length=r ∧
      Gadget.Realizes F .disequality (c • P.core phaseKernel f) ∧
      Disagreement m 4 (Signature.contract A₀ (c • P.core phaseKernel f))
        (Signature.contract A₁ (c • P.core phaseKernel f)) ∧
      Signature.contract A₀ (c • P.core phaseKernel f) ≠ 0 ∧
      Signature.contract A₁ (c • P.core phaseKernel f) ≠ 0 := by
  obtain ⟨P,hP,hout⟩ := localization_program hm r _ _ h
  let D := G.connections (by omega : 0<m)
  have he (i : PhaseLabel m) (a b : Bool) : D.binary i.1 i.2 (!a) (!b)=D.multiplier i.1 i.2*phaseKernel i a b := by
    rw [D.normalization]
    exact congrArg (D.multiplier i.1 i.2 * ·) (connection_entry i.1 i.2.val a b)
  obtain ⟨c,hc,hreal⟩ := P.realizes_core F phaseKernel (fun i => D.binary i.1 i.2)
    (fun i => D.multiplier i.1 i.2) (fun i => D.multiplier_ne_zero i.1 i.2)
    (fun i => D.actual i.1 i.2) he (by norm_num) f hf
  have hd : Disagreement m 4 (Signature.contract A₀ (c • P.core phaseKernel f))
      (Signature.contract A₁ (c • P.core phaseKernel f)) := by
    rw [contract_smul,contract_smul,P.inherited_card,P.inherited_card]
    exact hout.scale c hc
  exact ⟨P,c,hc,hP,hreal,hd,hd.nonzero (by omega)⟩

end Holant.Dihedral.TwoCardLocalization
