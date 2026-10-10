import Holant.Proofs.Dichotomy.Closure.Icosahedral.GlobalCloseCompletionIcosahedralModel
import Holant.Certificates.TetrahedralPreservers.Zero
import Holant.Certificates.TetrahedralPreservers.InvertibleAction
import Holant.Certificates.TetrahedralPreservers.NormalFormTransport
import Holant.Proofs.Dichotomy.Closure.Tetrahedral.GlobalCloseCompletionTetrahedralCurrent

/-! Generic I/opposite-I coefficient proof extracted from Preserver/Source.
No old saved-State dispatcher or caller-supplied classification is imported.
This candidate retains the actual full sixty-point hypotheses and proof. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 32768

noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIcosahedral.Preserver.Completion
open Holant Holant.Certificates Holant.Certificates.MatchingProductBridge
open Holant.Certificates.PlatonicIncidence Holant.Certificates.TetrahedralPreservers
open Holant.LocalDrafts.FinitePGL2.Stabilization
open scoped BigOperators Matrix

def point (opposite : Bool) (i : Fin 60) : V := coordinates (Dictionary.kernel opposite i)

theorem direction_det_ne_zero (opposite : Bool) {K : BinaryMatrix}
    (hK : Dictionary.direction opposite K) : K.det ≠ 0 := by
  cases opposite
  · exact groupDirection_det_ne_zero .icosahedral hK
  · exact OppositeIcosahedral.Direction.det_ne_zero hK

theorem direction_mul (opposite : Bool) {U W : BinaryMatrix}
    (hU : Dictionary.direction opposite U) (hW : Dictionary.direction opposite W) :
    Dictionary.direction opposite (U * W) := by
  cases opposite
  · exact RainbowOrbit.groupDirection_mul .icosahedral hU hW
  · exact OppositeIcosahedral.Direction.mul hU hW

private theorem opposite_transpose_conjugate (U : BinaryMatrix) :
    (OppositeIcosahedral.conjugate U).transpose=(-1 : ℂ) •
      OppositeIcosahedral.conjugate ((Matrix.of Q3)*U.transpose*(Matrix.of Q3)) := by
  ext a b
  cases a <;> cases b <;>
    simp [OppositeIcosahedral.conjugate,OppositeIcosahedral.D,OppositeIcosahedral.Dinv,
      Q0,Q3,Signature.equality,Matrix.mul_apply,Matrix.smul_apply] <;>
    ring_nf <;> simp [Complex.I_sq] <;> ring

private theorem opposite_transpose {U : BinaryMatrix}
    (hU : OppositeIcosahedral.Direction U) : OppositeIcosahedral.Direction U.transpose := by
  obtain ⟨V,hV,rfl⟩ := (OppositeIcosahedral.direction_iff_conjugate U).mp hU
  rw [opposite_transpose_conjugate]
  apply OppositeIcosahedral.Direction.smul _ (by norm_num)
  apply OppositeIcosahedral.conjugate_standard
  have hQ : groupDirection .icosahedral (Matrix.of Q3) := quaternion_axis_direction .icosahedral 3
  exact RainbowOrbit.groupDirection_mul .icosahedral
    (RainbowOrbit.groupDirection_mul .icosahedral hQ
      (MatchingProductBridge.groupDirection_transpose .icosahedral hV)) hQ

theorem direction_transpose (opposite : Bool) {U : BinaryMatrix}
    (hU : Dictionary.direction opposite U) : Dictionary.direction opposite U.transpose := by
  cases opposite
  · exact MatchingProductBridge.groupDirection_transpose .icosahedral hU
  · exact opposite_transpose hU

theorem direction_ne_zero (opposite : Bool) {K : BinaryMatrix}
    (hK : Dictionary.direction opposite K) : K ≠ 0 := by
  intro hz
  exact direction_det_ne_zero opposite hK (by simp [hz])

theorem point_mem (opposite : Bool) (i : Fin 60) : point opposite i ∈ roots opposite :=
  ⟨Dictionary.kernel opposite i,Dictionary.kernel_mem opposite i,rfl⟩

theorem point_ne_zero (opposite : Bool) (i : Fin 60) : point opposite i ≠ 0 := by
  intro hz
  apply direction_ne_zero opposite (Dictionary.kernel_mem opposite i)
  apply coordinates.injective
  simpa only [point,map_zero] using hz

@[simp] theorem assemble_point (opposite : Bool) (i : Fin 60) :
    assemble (point opposite i) = Dictionary.kernel opposite i :=
  assemble_coefficient _

theorem point_projectively_injective (opposite : Bool) (i j : Fin 60) (c : ℂ)
    (h : point opposite i = c • point opposite j) : i = j := by
  apply Dictionary.kernel_projectively_injective opposite i j c
  apply coordinates.injective
  simpa only [point,map_smul] using h

theorem roots_saturated (opposite : Bool) : Saturated (roots opposite) := by
  rintro r ⟨K,hK,rfl⟩ c hc
  exact ⟨c • K,Dictionary.scale opposite hK hc,map_smul coordinates c K⟩

/-- This use of T is ONLY a spanning test, never a restriction on H4 images. -/
theorem roots_axis (opposite : Bool) (i : Fin 4) : Pi.single i 1 ∈ roots opposite := by
  rw [←coordinates_basis]
  refine ⟨Matrix.of (quaternionBasis i),?_,rfl⟩
  cases opposite
  · exact OppositeIcosahedral.tetrahedral_standard (quaternion_axis_direction .tetrahedral i)
  · exact OppositeIcosahedral.Direction.of_tetrahedral (quaternion_axis_direction .tetrahedral i)

theorem roots_detects (opposite : Bool) : Detects (roots opposite) := by
  intro v hv
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hv
  refine ⟨Pi.single i 1,roots_axis opposite i,?_⟩
  rw [pairing_axis]
  apply mul_ne_zero _ hi
  intro hz
  have hs := signs_square i
  simp [hz] at hs

theorem roots_iff (opposite : Bool) (r : V) : r ∈ roots opposite ↔
    ∃ i : Fin 60, ∃ c : ℂ, c ≠ 0 ∧ r = c • point opposite i := by
  constructor
  · rintro ⟨K,hK,rfl⟩
    obtain ⟨i,c,hc,rfl⟩ := Dictionary.complete opposite K hK
    exact ⟨i,c,hc,map_smul coordinates c _⟩
  · rintro ⟨i,c,hc,rfl⟩
    exact roots_saturated opposite (point_mem opposite i) hc

/-- Complete classification of arbitrary COMPLEX rank-one H4 preservers. -/
theorem rank_one_complete (opposite : Bool) (A : End) (hr : A.rank = 1) :
    TwoSided (roots opposite) A ↔ ∃ i j : Fin 60, ∃ c : ℂ, c ≠ 0 ∧
      A = c • outer (point opposite i) (point opposite j) := by
  rw [rank_one_twoSided_iff (roots_saturated opposite) (roots_detects opposite) A hr]
  constructor
  · rintro ⟨u,v,hu,hv,rfl⟩
    obtain ⟨i,c,hc,rfl⟩ := (roots_iff opposite u).mp hu
    obtain ⟨j,d,hd,rfl⟩ := (roots_iff opposite v).mp hv
    exact ⟨i,j,c*d,mul_ne_zero hc hd,outer_smul _ _ c d⟩
  · rintro ⟨i,j,c,hc,rfl⟩
    refine ⟨c • point opposite i,point opposite j,
      roots_saturated opposite (point_mem opposite i) hc,point_mem opposite j,?_⟩
    simpa using (outer_smul (point opposite i) (point opposite j) c 1).symm

theorem outer_pair_unique (opposite : Bool) (a b : Fin 60 × Fin 60) (c : ℂ)
    (h : outer (point opposite a.1) (point opposite a.2) =
      c • outer (point opposite b.1) (point opposite b.2)) : a = b := by
  obtain ⟨d,hd⟩ := outer_proportional_left (point_ne_zero opposite a.2) h
  have hl := point_projectively_injective opposite a.1 b.1 d hd
  have hs := congrArg sharp h
  simp only [sharp_outer,sharp_smul] at hs
  obtain ⟨e,he⟩ := outer_proportional_left (point_ne_zero opposite a.1) hs
  exact Prod.ext hl (point_projectively_injective opposite a.2 b.2 e he)

def rankOneClass (opposite : Bool) (ij : Fin 60 × Fin 60) : RankOneClass (roots opposite) :=
  ⟨Projectivization.mk ℂ (outer (point opposite ij.1) (point opposite ij.2))
    (outer_ne_zero (point_ne_zero opposite _) (point_ne_zero opposite _)),
    _,outer_ne_zero (point_ne_zero opposite _) (point_ne_zero opposite _),
    rank_outer (point_ne_zero opposite _) (point_ne_zero opposite _),
    twoSided_outer (roots_saturated opposite) (point_mem opposite _) (point_mem opposite _),rfl⟩

theorem rankOneClass_bijective (opposite : Bool) : Function.Bijective (rankOneClass opposite) := by
  constructor
  · intro a b h
    have hh := congrArg Subtype.val h
    obtain ⟨c,hc⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp hh
    exact outer_pair_unique opposite a b c hc.symm
  · rintro ⟨q,A,hA,hr,hp,hq⟩
    obtain ⟨i,j,c,hc,he⟩ := (rank_one_complete opposite A hr).mp hp
    refine ⟨(i,j),Subtype.ext ?_⟩
    change Projectivization.mk ℂ (outer (point opposite i) (point opposite j)) _ = q
    rw [hq]
    symm
    exact (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr ⟨c,he.symm⟩

def rankOneEquiv (opposite : Bool) : (Fin 60 × Fin 60) ≃ RankOneClass (roots opposite) :=
  Equiv.ofBijective (rankOneClass opposite) (rankOneClass_bijective opposite)

/-- 3600 counts actual projective complex maps, not just certificate rows. -/
theorem rank_one_count (opposite : Bool) : Nat.card (RankOneClass (roots opposite)) = 3600 := by
  rw [←Nat.card_congr (rankOneEquiv opposite)]
  norm_num

private theorem reconstruct_smul (c : ℂ) (A : End) :
    reconstruct (c • A) = c • reconstruct A := by
  have ha (r : V) : assemble (c • r) = c • assemble r := coordinates.symm.map_smul c r
  funext x
  change (∑ i : Fin 4, Holant.Platonic.FixedMatchingRuling.Physical.quaternionDual i (x 0) (x 1) *
    assemble (c • (fun j => A j i)) (x 2) (x 3)) =
      c * (∑ i : Fin 4, Holant.Platonic.FixedMatchingRuling.Physical.quaternionDual i (x 0) (x 1) *
        assemble (fun j => A j i) (x 2) (x 3))
  simp only [ha,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  change _ * (c * _) = _
  ring

/-- A constructed matching has its literal ordered 2|2 ProperSplit. -/
private def matchingSplit (r : Fin 3) (U W : BinaryMatrix) (c : ℂ) (hc : c ≠ 0) :
    ProperSplit (⟨4,c • matchingProduct r U W⟩ : AnySignature ℂ)
      ⟨2,Holant.Projective.BoundedTorsion.binarySignature U⟩
      ⟨2,Holant.Projective.BoundedTorsion.binarySignature W⟩ where
  left_pos := by change 0 < (2 : ℕ); decide
  right_pos := by change 0 < (2 : ℕ); decide
  ports := finSumFinEquiv.trans (GlobalCloseCompletionTetrahedralClassifier.matchingFrame r)
  scale := Units.mk0 c hc
  equation := by
    have h := congrArg (fun q : FourTensor => c • q)
      (GlobalCloseCompletionTetrahedralCurrent.matching_tensor r U W)
    exact h

/-- The full-I rank-one classification produces the ACTUAL binary factors
and nonzero scalar on the original pair ports. No matching target is given. -/
theorem rank_one_literal_factor (opposite : Bool) (q : FourTensor)
    (hr : (cardMatrix q).rank = 1) (h : TwoSided (roots opposite) (cardMatrix q)) :
    ∃ i j : Fin 60, ∃ c : ℂ, c ≠ 0 ∧
      q = (c * (2 : ℂ)⁻¹) • P0 (Dictionary.kernel opposite j) (Dictionary.kernel opposite i) ∧
      (Dictionary.kernel opposite j).det ≠ 0 ∧ (Dictionary.kernel opposite i).det ≠ 0 ∧
      ∃ a b : AnySignature ℂ, Nonempty (ProperSplit (⟨4,q⟩ : AnySignature ℂ) a b) := by
  obtain ⟨i,j,c,hc,he⟩ := (rank_one_complete opposite (cardMatrix q) hr).mp h
  have hq : q = (c * (2 : ℂ)⁻¹) •
      P0 (Dictionary.kernel opposite j) (Dictionary.kernel opposite i) := by
    calc
      q = reconstruct (cardMatrix q) := (reconstruct_cardMatrix q).symm
      _ = reconstruct (c • outer (point opposite i) (point opposite j)) := congrArg reconstruct he
      _ = c • reconstruct (outer (point opposite i) (point opposite j)) := reconstruct_smul c _
      _ = _ := by rw [reconstruct_outer,assemble_point,assemble_point,smul_smul]
  refine ⟨i,j,c,hc,hq,
    direction_det_ne_zero opposite (Dictionary.kernel_mem opposite j),
    direction_det_ne_zero opposite (Dictionary.kernel_mem opposite i),?_⟩
  rw [hq]
  exact ⟨_,_,⟨matchingSplit 0 (Dictionary.kernel opposite j) (Dictionary.kernel opposite i)
    (c * (2 : ℂ)⁻¹) (mul_ne_zero hc (by norm_num))⟩⟩

private theorem pairing_ext {u v : V} (h : ∀ r : V, pairing r u = pairing r v) : u = v := by
  funext i
  have hh : frobeniusSigns i * u i = frobeniusSigns i * v i := by
    simpa [pairing,Pi.single_apply] using h (Pi.single i 1)
  have hs : frobeniusSigns i ≠ 0 := by
    intro hz
    have hsq := signs_square i
    simp [hz] at hsq
  exact mul_left_cancel₀ hs hh

private theorem frobenius_sandwich (U W R S : BinaryMatrix) :
    (∑ a : Bool, ∑ b : Bool, (U * R * W) a b * S a b) =
      ∑ a : Bool, ∑ b : Bool, R a b * (U.transpose * S * W.transpose) a b := by
  simp only [Fintype.sum_bool,Matrix.mul_apply,Matrix.transpose_apply]
  ring

private theorem frobenius_transposeSandwich (U W R S : BinaryMatrix) :
    (∑ a : Bool, ∑ b : Bool, (U * R.transpose * W) a b * S a b) =
      ∑ a : Bool, ∑ b : Bool, R a b * (W * S.transpose * U) a b := by
  simp only [Fintype.sum_bool,Matrix.mul_apply,Matrix.transpose_apply]
  ring

private theorem coordinate_assemble (r : V) : coordinates (assemble r) = r :=
  coordinates.apply_symm_apply r

/-- Literal bilinear Frobenius sharp, with no Hermitian conjugation. -/
theorem sharp_sandwich (U W : BinaryMatrix) :
    sharp (sandwich U W) = sandwich U.transpose W.transpose := by
  apply matrix_ext_action
  intro r
  apply pairing_ext
  intro s
  rw [←pairing_adjoint,sandwich_action,sandwich_action]
  have hh := frobenius_sandwich U W (assemble s) (assemble r)
  simp only [frobenius_pairing,coordinate_assemble] at hh
  exact mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) hh

theorem sharp_transposeSandwich (U W : BinaryMatrix) :
    sharp (transposeSandwich U W) = transposeSandwich W U := by
  apply matrix_ext_action
  intro r
  apply pairing_ext
  intro s
  rw [←pairing_adjoint,transposeSandwich_action,transposeSandwich_action]
  have hh := frobenius_transposeSandwich U W (assemble s) (assemble r)
  simp only [frobenius_pairing,coordinate_assemble] at hh
  exact mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) hh

theorem sandwich_one_sided (opposite : Bool) {U W : BinaryMatrix}
    (hU : Dictionary.direction opposite U) (hW : Dictionary.direction opposite W) :
    OneSided (roots opposite) (sandwich U W) := by
  intro r hr
  have hR : Dictionary.direction opposite (assemble r) :=
    (mem_coefficientSet_iff _ r).mp hr
  rw [sandwich_action]
  exact Or.inr ⟨_,direction_mul opposite (direction_mul opposite hU hR) hW,rfl⟩

theorem transposeSandwich_one_sided (opposite : Bool) {U W : BinaryMatrix}
    (hU : Dictionary.direction opposite U) (hW : Dictionary.direction opposite W) :
    OneSided (roots opposite) (transposeSandwich U W) := by
  intro r hr
  have hR : Dictionary.direction opposite (assemble r) :=
    (mem_coefficientSet_iff _ r).mp hr
  rw [transposeSandwich_action]
  exact Or.inr ⟨_,direction_mul opposite
    (direction_mul opposite hU (direction_transpose opposite hR)) hW,rfl⟩

theorem sandwich_two_sided (opposite : Bool) {U W : BinaryMatrix}
    (hU : Dictionary.direction opposite U) (hW : Dictionary.direction opposite W) :
    TwoSided (roots opposite) (sandwich U W) := by
  refine ⟨sandwich_one_sided opposite hU hW,?_⟩
  rw [sharp_sandwich]
  exact sandwich_one_sided opposite (direction_transpose opposite hU) (direction_transpose opposite hW)

theorem transposeSandwich_two_sided (opposite : Bool) {U W : BinaryMatrix}
    (hU : Dictionary.direction opposite U) (hW : Dictionary.direction opposite W) :
    TwoSided (roots opposite) (transposeSandwich U W) := by
  refine ⟨transposeSandwich_one_sided opposite hU hW,?_⟩
  rw [sharp_transposeSandwich]
  exact transposeSandwich_one_sided opposite hW hU

private theorem sandwich_cancel {U W : BinaryMatrix} (hU : U.det ≠ 0) (hW : W.det ≠ 0)
    (R : BinaryMatrix) : U⁻¹ * (U * R * W) * W⁻¹ = R := by
  calc
    _ = (U⁻¹ * U) * R * (W * W⁻¹) := by simp only [Matrix.mul_assoc]
    _ = R := by rw [Matrix.nonsing_inv_mul U (isUnit_iff_ne_zero.mpr hU),
      Matrix.mul_nonsing_inv W (isUnit_iff_ne_zero.mpr hW),Matrix.one_mul,Matrix.mul_one]

private theorem sandwich_binary_injective {U W : BinaryMatrix}
    (hU : U.det ≠ 0) (hW : W.det ≠ 0) :
    Function.Injective (fun R : BinaryMatrix => U * R * W) := by
  intro R S h
  have hh := congrArg (fun M : BinaryMatrix => U⁻¹ * M * W⁻¹) h
  simpa only [sandwich_cancel hU hW] using hh

theorem sandwich_rank_four {U W : BinaryMatrix} (hU : U.det ≠ 0) (hW : W.det ≠ 0) :
    (sandwich U W).rank = 4 := by
  apply (rank_four_iff_det_ne_zero _).mpr
  apply isUnit_iff_ne_zero.mp
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro r s h
  simp only [sandwich_action] at h
  exact coordinates.symm.injective (sandwich_binary_injective hU hW (coordinates.injective h))

theorem transposeSandwich_rank_four {U W : BinaryMatrix} (hU : U.det ≠ 0) (hW : W.det ≠ 0) :
    (transposeSandwich U W).rank = 4 := by
  apply (rank_four_iff_det_ne_zero _).mpr
  apply isUnit_iff_ne_zero.mp
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro r s h
  simp only [transposeSandwich_action] at h
  have ht := sandwich_binary_injective hU hW (coordinates.injective h)
  have ha : assemble r = assemble s := by
    have hh := congrArg Matrix.transpose ht
    simpa only [Matrix.transpose_transpose] using hh
  exact coordinates.symm.injective ha

/-- Exactly 7200 parameter choices; no assertion of projective uniqueness
or exhaustive rank-four coverage is made for this family. -/
def candidate (opposite transpose : Bool) (i j : Fin 60) : End :=
  if transpose then transposeSandwich (Dictionary.kernel opposite i) (Dictionary.kernel opposite j)
  else sandwich (Dictionary.kernel opposite i) (Dictionary.kernel opposite j)

theorem candidate_two_sided (opposite transpose : Bool) (i j : Fin 60) :
    TwoSided (roots opposite) (candidate opposite transpose i j) := by
  cases transpose
  · exact sandwich_two_sided opposite (Dictionary.kernel_mem opposite i) (Dictionary.kernel_mem opposite j)
  · exact transposeSandwich_two_sided opposite (Dictionary.kernel_mem opposite i) (Dictionary.kernel_mem opposite j)

theorem candidate_rank_four (opposite transpose : Bool) (i j : Fin 60) :
    (candidate opposite transpose i j).rank = 4 := by
  have hi := direction_det_ne_zero opposite (Dictionary.kernel_mem opposite i)
  have hj := direction_det_ne_zero opposite (Dictionary.kernel_mem opposite j)
  cases transpose
  · exact sandwich_rank_four hi hj
  · exact transposeSandwich_rank_four hi hj

theorem candidate_reconstruction (opposite transpose : Bool) (i j : Fin 60) :
    reconstruct (candidate opposite transpose i j) =
      if transpose then matchingProduct 2 (Dictionary.kernel opposite j) (Dictionary.kernel opposite i).transpose
      else matchingProduct 1 (Dictionary.kernel opposite i).transpose (Dictionary.kernel opposite j) := by
  cases transpose
  · exact reconstruct_sandwich _ _
  · exact reconstruct_transposeSandwich _ _

/-- Produce the actual nonsingular factors and crossing matching, rather
than asking a caller for a desired factorization or normal form. -/
theorem candidate_binary_factors (opposite transpose : Bool) (i j : Fin 60) :
    ∃ r : Fin 3, ∃ U W : BinaryMatrix, U.det ≠ 0 ∧ W.det ≠ 0 ∧
      reconstruct (candidate opposite transpose i j) = matchingProduct r U W := by
  have hi := direction_det_ne_zero opposite (Dictionary.kernel_mem opposite i)
  have hj := direction_det_ne_zero opposite (Dictionary.kernel_mem opposite j)
  have ht : (Dictionary.kernel opposite i).transpose.det ≠ 0 := by
    simpa only [Matrix.det_transpose] using hi
  cases transpose
  · exact ⟨1,(Dictionary.kernel opposite i).transpose,Dictionary.kernel opposite j,ht,hj,
      candidate_reconstruction opposite false i j⟩
  · exact ⟨2,Dictionary.kernel opposite j,(Dictionary.kernel opposite i).transpose,hj,ht,
      candidate_reconstruction opposite true i j⟩

/-- Actual rank-four candidates have an explicit proper original-port split,
including EVERY nonzero choice of their exterior scalar. -/
theorem candidate_tensor_split (opposite transpose : Bool) (i j : Fin 60) (c : ℂ) (hc : c ≠ 0) :
    ∃ a b : AnySignature ℂ, Nonempty
      (ProperSplit (⟨4,reconstruct (c • candidate opposite transpose i j)⟩ : AnySignature ℂ) a b) := by
  obtain ⟨r,U,W,hU,hW,he⟩ := candidate_binary_factors opposite transpose i j
  rw [reconstruct_smul,he]
  exact ⟨_,_,⟨matchingSplit r U W c hc⟩⟩

/-- Injectivity and the COMPLETE actual sixty classes produce the
permutation; a permutation or desired normal form is not a premise. -/
theorem invertible_permutation (opposite : Bool) (A : End) (hA : A.det ≠ 0)
    (h : OneSided (roots opposite) A) :
    ∃ σ : Equiv.Perm (Fin 60), ∃ c : Fin 60 → ℂ,
      (∀ i, c i ≠ 0) ∧ ∀ i, A *ᵥ point opposite i = c i • point opposite (σ i) := by
  have hi := Matrix.mulVec_injective_of_det_ne_zero hA
  have hc (i : Fin 60) : ∃ j : Fin 60, ∃ c : ℂ, c ≠ 0 ∧
      A *ᵥ point opposite i = c • point opposite j := by
    rcases h _ (point_mem opposite i) with hz | hm
    · exact False.elim (point_ne_zero opposite i (hi (by simpa using hz)))
    · exact (roots_iff opposite _).mp hm
  choose σ c hc he using hc
  have hσ : Function.Injective σ := by
    intro i j hij
    have heq : A *ᵥ point opposite i = (c i * (c j)⁻¹) • (A *ᵥ point opposite j) := by
      rw [he i,he j,hij,smul_smul]
      congr 1
      field_simp [hc j]
    rw [←Matrix.mulVec_smul] at heq
    exact point_projectively_injective opposite i j _ (hi heq)
  let e : Equiv.Perm (Fin 60) := Equiv.ofBijective σ ⟨hσ,Finite.surjective_of_injective hσ⟩
  exact ⟨e,c,hc,he⟩

theorem rank_four_two_permutations (opposite : Bool) (A : End) (hr : A.rank = 4)
    (h : TwoSided (roots opposite) A) :
    ∃ σ τ : Equiv.Perm (Fin 60), ∃ c d : Fin 60 → ℂ,
      (∀ i, c i ≠ 0) ∧ (∀ i, d i ≠ 0) ∧
      (∀ i, A *ᵥ point opposite i = c i • point opposite (σ i)) ∧
      (∀ i, sharp A *ᵥ point opposite i = d i • point opposite (τ i)) := by
  obtain ⟨σ,c,hc,he⟩ := invertible_permutation opposite A
    ((rank_four_iff_det_ne_zero A).mp hr) h.1
  have hJ : J.det ≠ 0 := by
    have hh := congrArg Matrix.det J_square
    simp only [Matrix.det_mul,Matrix.det_one] at hh
    intro hz
    simp [hz] at hh
  have hs : (sharp A).rank = 4 := by
    rw [sharp,Matrix.rank_mul_eq_left_of_det_ne_zero _ _ hJ,
      Matrix.rank_mul_eq_right_of_det_ne_zero _ _ hJ,Matrix.rank_transpose]
    exact hr
  obtain ⟨τ,d,hd,hf⟩ := invertible_permutation opposite (sharp A)
    ((rank_four_iff_det_ne_zero _).mp hs) h.2
  exact ⟨σ,τ,c,d,hc,hd,he,hf⟩

theorem prime_rank_not_zero (q : FourTensor) (hp : Prime (⟨4,q⟩ : AnySignature ℂ)) :
    (cardMatrix q).rank ≠ 0 := by
  intro hr
  have hz := (TetrahedralPreservers.rank_zero_iff (cardMatrix q)).mp hr
  apply hp.1
  rw [←reconstruct_cardMatrix q,hz]
  funext x
  simp [reconstruct,assemble]

theorem prime_rank_not_one (opposite : Bool) (q : FourTensor)
    (hp : Prime (⟨4,q⟩ : AnySignature ℂ)) (h : TwoSided (roots opposite) (cardMatrix q)) :
    (cardMatrix q).rank ≠ 1 := by
  intro hr
  obtain ⟨i,j,c,hc,hq,hU,hW,hs⟩ := rank_one_literal_factor opposite q hr h
  exact hp.2 hs

theorem prime_not_candidate (opposite : Bool) (q : FourTensor)
    (hp : Prime (⟨4,q⟩ : AnySignature ℂ)) (transpose : Bool) (i j : Fin 60) (c : ℂ) (hc : c ≠ 0) :
    cardMatrix q ≠ c • candidate opposite transpose i j := by
  intro he
  have hq : q = reconstruct (c • candidate opposite transpose i j) :=
    (reconstruct_cardMatrix q).symm.trans (congrArg reconstruct he)
  apply hp.2
  rw [hq]
  exact candidate_tensor_split opposite transpose i j c hc

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIcosahedral.Preserver.Completion
end
