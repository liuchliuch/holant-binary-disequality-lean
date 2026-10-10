import Holant.Platonic.StabilizerErasure.ColumnForms
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! The computational-basis and full-rank steps after simultaneous Z
coordinates have actually been obtained.  This file does not assume that
those Clifford coordinates exist and does not claim the missing quadratic
phase extraction. -/
namespace Holant.Platonic.StabilizerErasure
open Holant Holant.Tractable.AffinePhase Holant.Tractable.TwoTranslate
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.AffinePatching Holant.ReedMuller.CharacterFlat
open Holant.Platonic.StabilizerLine
open scoped BigOperators ComplexConjugate
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n k : ℕ}

def ket (z : Word n) : Signature ℂ n := fun w => if w=z then 1 else 0

@[simp] theorem hermitian_ket (z w : Word n) :
    hermitian (ket z) (ket w)=if z=w then 1 else 0 := by
  simp [hermitian,ket,eq_comm]

theorem ket_ne_zero (z : Word n) : ket z≠0 := by
  intro h
  have he := congrFun h z
  simp [ket] at he

/-- Simultaneous eigenvectors of all coordinate Z operators are supported
on exactly their joint binary eigenvalue word. -/
theorem simultaneous_z_support (f : Signature ℂ n) (z : BinaryVector n)
    (h : ∀r w,sign (vectorWord w r)*f w=sign (z r)*f w)
    (w : Word n) (hw : vectorWord w≠z) : f w=0 := by
  have he : ∃r,vectorWord w r≠z r := by
    by_contra hn
    apply hw
    ext r
    by_contra hr
    exact hn ⟨r,hr⟩
  obtain ⟨r,hr⟩ := he
  have hp := h r w
  rcases binary_cases (vectorWord w r) with ha|ha <;>
    rcases binary_cases (z r) with hb|hb
  all_goals simp only [ha,hb,sign_zero,sign_one,one_mul,neg_mul] at hp hr
  all_goals try exact (hr rfl).elim
  all_goals first | linear_combination hp/2 | linear_combination -hp/2

theorem simultaneous_z_column (f : Signature ℂ n) (z : BinaryVector n)
    (h : ∀r w,sign (vectorWord w r)*f w=sign (z r)*f w) :
    f=f (wordVector z) • ket (wordVector z) := by
  ext w
  by_cases hw : w=wordVector z
  · subst w;simp [ket]
  · have hz : vectorWord w≠z := by intro he;apply hw;simpa using congrArg wordVector he
    simp [ket,hw,simultaneous_z_support f z h w hz]

/-- Isometry forces the binary linear column map to be injective, without
silently including full rank in the column description. -/
theorem basis_column_map_injective (V : StabilizerIsometry k n)
    (c : BinaryVector n) (M : BinaryVector k →ₗ[ZMod 2] BinaryVector n)
    (a : BinaryVector k → ℂ)
    (h : ∀z,V.map (ket (wordVector z))=a z • ket (wordVector (c+M z))) :
    Function.Injective M := by
  have hn (z : BinaryVector k) : a z≠0 := by
    intro hz
    have hv : V.map (ket (wordVector z))=V.map 0 := by simp [h,hz]
    exact ket_ne_zero _ (V.injective hv)
  intro z w hzw
  by_contra hne
  have hw : wordVector z≠wordVector w := by
    intro he;apply hne;simpa using congrArg vectorWord he
  have hi := V.isometry (ket (wordVector z)) (ket (wordVector w))
  rw [h z,h w,hermitian_smul,hermitian_ket,hermitian_ket,if_neg hw,hzw] at hi
  simp only [ite_true,mul_one] at hi
  exact (mul_ne_zero (by simpa using hn z) (hn w)) hi

theorem basis_column_map_full_rank (V : StabilizerIsometry k n)
    (c : BinaryVector n) (M : BinaryVector k →ₗ[ZMod 2] BinaryVector n)
    (a : BinaryVector k → ℂ)
    (h : ∀z,V.map (ket (wordVector z))=a z • ket (wordVector (c+M z))) :
    Module.finrank (ZMod 2) M.range=k := by
  have hi := basis_column_map_injective V c M a h
  have hr := M.finrank_range_add_finrank_ker
  rw [LinearMap.ker_eq_bot.mpr hi] at hr
  simpa [BinaryVector] using hr

theorem z_coordinates_give_full_rank_columns (V : StabilizerIsometry k n)
    (c : BinaryVector n) (M : BinaryVector k →ₗ[ZMod 2] BinaryVector n)
    (h : ∀z r w,sign (vectorWord w r)*V.map (ket (wordVector z)) w=
      sign ((c+M z) r)*V.map (ket (wordVector z)) w) :
    ∃a : BinaryVector k → ℂ,(∀z,a z≠0) ∧
      (∀z,V.map (ket (wordVector z))=a z • ket (wordVector (c+M z))) ∧
      Module.finrank (ZMod 2) M.range=k := by
  let a := fun z => V.map (ket (wordVector z)) (wordVector (c+M z))
  have he (z) : V.map (ket (wordVector z))=a z • ket (wordVector (c+M z)) :=
    simultaneous_z_column _ _ (h z)
  refine ⟨a,?_,he,basis_column_map_full_rank V c M a he⟩
  intro z hz
  have hv : V.map (ket (wordVector z))=V.map 0 := by simp [he,hz]
  exact ket_ne_zero _ (V.injective hv)

end
end Holant.Platonic.StabilizerErasure
