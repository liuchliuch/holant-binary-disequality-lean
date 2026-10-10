import Holant.Platonic.StabilizerErasure.PhysicalAlignment
import Holant.Platonic.StabilizerErasure.NonzeroColumns
import Holant.Platonic.StabilizerCode.CommutingAlignmentErasure

/-! Actual physical and logical Clifford alignment produces affine basis
columns whenever every single-site erasure fails. Neither the alignments
nor the affine eigenvalue words are hypotheses. Quadratic phase extraction
is a separate remaining step. -/
namespace Holant.Platonic.StabilizerErasure
open Holant Holant.Tractable.AffinePhase Holant.Tractable.TwoTranslate
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.AffinePatching Holant.ReedMuller.CharacterFlat
open Holant.ReedMuller.RadonAccess
open Holant.Platonic.StabilizerLine Holant.Platonic.StabilizerCode
open scoped ComplexConjugate
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n k : ℕ}

def framedMap (V : StabilizerIsometry k n) (A : AnalyticClifford n) (B : AnalyticClifford k) :
    Signature ℂ k →ₗ[ℂ] Signature ℂ n :=
  A.operator.toLinearMap.comp (V.map.comp B.operator.symm.toLinearMap)

theorem framedMap_isometry (V : StabilizerIsometry k n)
    (A : AnalyticClifford n) (B : AnalyticClifford k) (f g : Signature ℂ k) :
    hermitian (framedMap V A B f) (framedMap V A B g)=hermitian f g := by
  change hermitian (A.operator (V.map (B.operator.symm f)))
    (A.operator (V.map (B.operator.symm g)))=_
  rw [A.unitary,V.isometry]
  simpa using (B.unitary (B.operator.symm f) (B.operator.symm g)).symm

theorem framedMap_injective (V : StabilizerIsometry k n)
    (A : AnalyticClifford n) (B : AnalyticClifford k) : Function.Injective (framedMap V A B) :=
  A.operator.injective.comp (V.injective.comp B.operator.symm.injective)

def columnLinearMap (b : Fin n → BinaryVector k) :
    BinaryVector k →ₗ[ZMod 2] BinaryVector n := LinearMap.pi (fun r => dotBilinear (b r))

@[simp] theorem columnLinearMap_apply (b : Fin n → BinaryVector k) (z : BinaryVector k) (r : Fin n) :
    columnLinearMap b z r=dot (b r) z := rfl

theorem siteZ_value (r : Fin (n+1)) (f : Signature ℂ (n+1)) (w : Word (n+1)) :
    siteAction r (qubitPauli 3) f w=sign (vectorWord w r)*f w := by
  cases hw : w r <;> simp [siteAction,qubitPauli,vectorWord,boolEquiv,hw]

theorem standardZ_ket (b z : BinaryVector k) :
    standardPauli 0 0 b (ket (wordVector z))=sign (dot b z) • ket (wordVector z) := by
  ext w
  rw [standardPauli_dot]
  by_cases hw : w=wordVector z
  · subst w;simp [ket]
  · simp [ket,hw]

theorem framed_basis_columns (V : StabilizerIsometry k (n+1))
    (h : ∀r : Fin (n+1),¬Correctable V r) :
    ∃p : Fin (n+1) → Fin 4,∃B : AnalyticClifford k,
      ∃c : BinaryVector (n+1),∃b : Fin (n+1) → BinaryVector k,
        (∀r,p r≠0 ∧ b r≠0) ∧
        ∀z,framedMap V (physicalAxisProgram p).clifford B (ket (wordVector z))=
          framedMap V (physicalAxisProgram p).clifford B (ket (wordVector z))
            (wordVector (c+columnLinearMap b z)) • ket (wordVector (c+columnLinearMap b z)) := by
  obtain ⟨p,Q,B,s,b,hp,hQ,hB⟩ := no_correctable_logical_clifford V h
  let A := (physicalAxisProgram p).clifford
  have hlogical (r : Fin (n+1)) (f : Signature ℂ k) :
      (Q r).run (B.operator.symm f)=
        sign (s r) • B.operator.symm (standardPauli 0 0 (b r) f) := by
    apply B.operator.injective
    rw [hB,map_smul,LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply]
  have hdiag (r : Fin (n+1)) (f : Signature ℂ k) :
      siteAction r (qubitPauli 3) (framedMap V A B f)=
        sign (s r) • framedMap V A B (standardPauli 0 0 (b r) f) := by
    change siteAction r (qubitPauli 3)
      ((physicalAxisProgram p).run (V.map (B.operator.symm f)))=_
    rw [←physicalAxisProgram_aligns p (fun r => (hp r).1),hQ,hlogical,map_smul]
    change A.operator (sign (s r) • V.map (B.operator.symm (standardPauli 0 0 (b r) f)))=_
    rw [map_smul]
    rfl
  refine ⟨p,B,s,b,hp,?_⟩
  intro z
  apply simultaneous_z_column
  intro r w
  have he := congrFun (hdiag r (ket (wordVector z))) w
  rw [siteZ_value,standardZ_ket,map_smul] at he
  simpa [Pi.smul_apply,smul_eq_mul,sign_add,mul_assoc] using he

theorem framed_column_full_rank (V : StabilizerIsometry k n)
    (A : AnalyticClifford n) (B : AnalyticClifford k)
    (c : BinaryVector n) (M : BinaryVector k →ₗ[ZMod 2] BinaryVector n)
    (a : BinaryVector k → ℂ)
    (h : ∀z,framedMap V A B (ket (wordVector z))=a z • ket (wordVector (c+M z))) :
    (∀z,a z≠0) ∧ Module.finrank (ZMod 2) M.range=k := by
  have hn (z : BinaryVector k) : a z≠0 := by
    intro hz
    have hv : framedMap V A B (ket (wordVector z))=framedMap V A B 0 := by simp [h,hz]
    exact ket_ne_zero _ (framedMap_injective V A B hv)
  refine ⟨hn,?_⟩
  have hi : Function.Injective M := by
    intro z w hzw
    by_contra hne
    have hw : wordVector z≠wordVector w := by
      intro he;apply hne;simpa using congrArg vectorWord he
    have he := framedMap_isometry V A B (ket (wordVector z)) (ket (wordVector w))
    rw [h z,h w,hermitian_smul,hermitian_ket,hermitian_ket,if_neg hw,hzw] at he
    simp only [ite_true,mul_one] at he
    exact (mul_ne_zero (by simpa using hn z) (hn w)) he
  have hr := M.finrank_range_add_finrank_ker
  rw [LinearMap.ker_eq_bot.mpr hi] at hr
  simpa [BinaryVector] using hr

/-- The affine basis-column conclusion with its genuine physical tensor of
axis Cliffords and logical Clifford, and both rank conditions derived.
Only the source's additional quadratic restriction on a remains open here. -/
theorem no_correctable_affine_columns (V : StabilizerIsometry k (n+1))
    (h : ∀r : Fin (n+1),¬Correctable V r) :
    ∃p : Fin (n+1) → Fin 4,∃B : AnalyticClifford k,
      ∃c : BinaryVector (n+1),∃b : Fin (n+1) → BinaryVector k,
        ∃a : BinaryVector k → ℂ,
          (∀r,p r≠0 ∧ b r≠0) ∧ (∀z,a z≠0) ∧
          Module.finrank (ZMod 2) (columnLinearMap b).range=k ∧
          ∀z,framedMap V (physicalAxisProgram p).clifford B (ket (wordVector z))=
            a z • ket (wordVector (c+columnLinearMap b z)) := by
  obtain ⟨p,B,c,b,hp,he⟩ := framed_basis_columns V h
  let a := fun z => framedMap V (physicalAxisProgram p).clifford B (ket (wordVector z))
    (wordVector (c+columnLinearMap b z))
  have ha := framed_column_full_rank V (physicalAxisProgram p).clifford B c (columnLinearMap b) a he
  exact ⟨p,B,c,b,a,hp,ha.1,ha.2,he⟩

end
end Holant.Platonic.StabilizerErasure
