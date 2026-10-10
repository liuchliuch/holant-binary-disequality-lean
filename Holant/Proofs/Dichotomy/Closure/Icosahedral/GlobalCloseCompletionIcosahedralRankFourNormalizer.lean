import Holant.Proofs.Dichotomy.Closure.Icosahedral.GlobalCloseCompletionIcosahedralRankFourConformal
import Holant.Certificates.TetrahedralPreservers.FullRankNormalForms
import Mathlib.Algebra.Group.Subgroup.Finite

/-! Generic I/opposite-I coefficient proof extracted from RankFour/Normalizer.
No old saved-State dispatcher or caller-supplied classification is imported.
This candidate retains the actual full sixty-point hypotheses and proof. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 32768

noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIcosahedral.RankFour
open Holant Holant.Certificates Holant.Certificates.MatchingProductBridge
open Holant.Certificates.PlatonicIncidence Holant.Certificates.TetrahedralPreservers
open Holant.Projective.BoundedTorsion Holant.Projective.FiniteGroupFacts
open Preserver.Completion
open scoped BigOperators Matrix

theorem dictionary_self_normalizing (opposite : Bool) :
    Subgroup.normalizer (Dictionary.group opposite : Set (PGL2 ℂ)) = Dictionary.group opposite := by
  cases opposite
  · exact icosahedral_normalizer
  · change Subgroup.normalizer
      ((modelPGL .icosahedral).map (MulAut.conj Placement.d).toMonoidHom : Set (PGL2 ℂ)) =
        (modelPGL .icosahedral).map (MulAut.conj Placement.d).toMonoidHom
    rw [←Subgroup.map_equiv_normalizer_eq (modelPGL .icosahedral) (MulAut.conj Placement.d),
      icosahedral_normalizer]

/-- This is a branch lemma consumed ONLY after the actual Segre producer.
The only supplied equations are its actual sandwich formula and the
original root-preserver property, not desired factor memberships. -/
theorem sandwich_directions (opposite : Bool) (U W : Matrix Bool Bool ℂ)
    (hU : U.det ≠ 0) (hW : W.det ≠ 0)
    (himage : ∀ K : Matrix Bool Bool ℂ, Dictionary.direction opposite K →
      Dictionary.direction opposite (U*K*W)) :
    Dictionary.direction opposite U ∧ Dictionary.direction opposite W := by
  let UG : Matrix.GeneralLinearGroup Bool ℂ := Matrix.GeneralLinearGroup.mkOfDetNeZero U hU
  let WG : Matrix.GeneralLinearGroup Bool ℂ := Matrix.GeneralLinearGroup.mkOfDetNeZero W hW
  let u : PGL2 ℂ := pglMk ℂ UG
  let w : PGL2 ℂ := pglMk ℂ WG
  let H : Subgroup (PGL2 ℂ) := Dictionary.group opposite
  have hUG : (UG : Matrix Bool Bool ℂ) = U := rfl
  have hWG : (WG : Matrix Bool Bool ℂ) = W := rfl
  have hone : Dictionary.direction opposite (1 : Matrix Bool Bool ℂ) := by
    simpa only [Matrix.GeneralLinearGroup.coe_one] using
      (Dictionary.matrix_iff opposite (1 : Matrix.GeneralLinearGroup Bool ℂ)).mp
        (by simpa only [map_one] using H.one_mem)
  have hUW : Dictionary.direction opposite (U*W) := by
    simpa only [Matrix.mul_one] using himage 1 hone
  have huv : u*w ∈ H := by
    have hmatrix : (↑(UG*WG) : Matrix Bool Bool ℂ) = U*W := by
      rw [Matrix.GeneralLinearGroup.coe_mul,hUG,hWG]
    have hm := (Dictionary.matrix_iff opposite (UG*WG)).mpr
      (hmatrix.symm ▸ hUW)
    simpa only [map_mul] using hm
  have maps : ∀ q : PGL2 ℂ, q ∈ H → u*q*w ∈ H := by
    intro q
    refine Quotient.inductionOn q ?_
    intro K hq
    have hK := (Dictionary.matrix_iff opposite K).mp hq
    have hmatrix : (↑(UG*K*WG) : Matrix Bool Bool ℂ) = U*(K : Matrix Bool Bool ℂ)*W := by
      rw [Matrix.GeneralLinearGroup.coe_mul,Matrix.GeneralLinearGroup.coe_mul,hUG,hWG]
    have hmat : Dictionary.direction opposite (↑(UG*K*WG) : Matrix Bool Bool ℂ) :=
      hmatrix.symm ▸ himage (K : Matrix Bool Bool ℂ) hK
    have hm := (Dictionary.matrix_iff opposite (UG*K*WG)).mpr hmat
    change pglMk ℂ UG * pglMk ℂ K * pglMk ℂ WG ∈ Dictionary.group opposite
    simpa only [map_mul] using hm
  have conjugates (q : PGL2 ℂ) (hq : q ∈ H) : w⁻¹*q*w ∈ H := by
    have hm := H.mul_mem (H.inv_mem huv) (maps q hq)
    have he : w⁻¹*q*w = (u*w)⁻¹*(u*q*w) := by group
    rw [he]
    exact hm
  let e : PGL2 ℂ ≃* PGL2 ℂ := MulAut.conj w⁻¹
  let S : Subgroup (PGL2 ℂ) := H.map e.toMonoidHom
  have hle : S ≤ H := by
    rintro q ⟨r,hr,rfl⟩
    change (MulAut.conj w⁻¹) r ∈ H
    simpa only [MulAut.conj_apply,inv_inv] using conjugates r hr
  have hcard : Nat.card S = Nat.card H :=
    (Nat.card_congr (H.equivMapOfInjective e.toMonoidHom e.injective).toEquiv).symm
  letI : Finite H := Nat.finite_of_card_ne_zero (by
    change Nat.card (Dictionary.group opposite) ≠ 0
    rw [Dictionary.group_card]
    decide)
  have hS : S=H := Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm)
  have hconj : H.map (MulAut.conj w⁻¹).toMonoidHom = H := hS
  have hinv : w⁻¹ ∈ Subgroup.normalizer (H : Set (PGL2 ℂ)) :=
    (Subgroup.mem_normalizer_iff_map_conj_eq (H := H) (g := w⁻¹)).mpr hconj
  have hw : w ∈ Subgroup.normalizer (H : Set (PGL2 ℂ)) := by
    simpa only [inv_inv] using (Subgroup.normalizer (H : Set (PGL2 ℂ))).inv_mem hinv
  have hwH : w ∈ H := by
    have hnormal : Subgroup.normalizer (H : Set (PGL2 ℂ)) = H :=
      dictionary_self_normalizing opposite
    exact (congrArg (fun J : Subgroup (PGL2 ℂ) => w ∈ J) hnormal).mp hw
  have huH : u ∈ H := by
    have hm := H.mul_mem huv (H.inv_mem hwH)
    simpa only [mul_assoc,mul_inv_cancel,mul_one] using hm
  have hu : Dictionary.direction opposite (UG : Matrix Bool Bool ℂ) :=
    (Dictionary.matrix_iff opposite UG).mp huH
  have hw' : Dictionary.direction opposite (WG : Matrix Bool Bool ℂ) :=
    (Dictionary.matrix_iff opposite WG).mp hwH
  exact ⟨hUG ▸ hu,hWG ▸ hw'⟩

theorem transposeSandwich_directions (opposite : Bool) (U W : Matrix Bool Bool ℂ)
    (hU : U.det ≠ 0) (hW : W.det ≠ 0)
    (himage : ∀ K : Matrix Bool Bool ℂ, Dictionary.direction opposite K →
      Dictionary.direction opposite (U*K.transpose*W)) :
    Dictionary.direction opposite U ∧ Dictionary.direction opposite W := by
  apply sandwich_directions opposite U W hU hW
  intro K hK
  simpa only [Matrix.transpose_transpose] using
    himage K.transpose (direction_transpose opposite hK)

/-- Same literal finite kernels, with the exact actual exterior scalar.
This lemma classifies the factors PRODUCED by Segre; it does not assert
that a free supplied candidate exhausts arbitrary complex operators. -/
theorem factors_dictionary (opposite transpose : Bool) (U W : Matrix Bool Bool ℂ)
    (hU : Dictionary.direction opposite U) (hW : Dictionary.direction opposite W) :
    ∃ i j : Fin 60, ∃ c : ℂ, c ≠ 0 ∧
      kindSandwich transpose U W = c • candidate opposite transpose i j := by
  obtain ⟨i,c,hc,rfl⟩ := Dictionary.complete opposite U hU
  obtain ⟨j,d,hd,rfl⟩ := Dictionary.complete opposite W hW
  refine ⟨i,j,c*d,mul_ne_zero hc hd,?_⟩
  rw [kindSandwich_smul_left,kindSandwich_smul_right,smul_smul]
  rfl

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIcosahedral.RankFour
end
