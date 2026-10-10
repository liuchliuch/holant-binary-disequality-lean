import Holant.Proofs.Dichotomy.Closure.Icosahedral.GlobalCloseCompletionIcosahedralRankFourIncidence
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! Generic I/opposite-I coefficient proof extracted from RankFour/Conformal.
No old saved-State dispatcher or caller-supplied classification is imported.
This candidate retains the actual full sixty-point hypotheses and proof. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 32768

noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIcosahedral.RankFour
open Holant Holant.Certificates Holant.Certificates.MatchingProductBridge
open Holant.Certificates.PlatonicIncidence Holant.Certificates.TetrahedralPreservers
open Holant.Certificates.RainbowOrbit
open Preserver.Completion
open scoped BigOperators Matrix

def axis (i : Fin 4) : Fin 60 := ⟨i.val,by omega⟩

theorem axis_injective : Function.Injective axis := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 60 => k.val) h)

private theorem standardPoint_literal (i : Fin 60) :
    standardPoint i = fun j : Fin 4 => (GoldenInt.eval (icosahedralRaw i j) : ℂ) := by
  funext j
  exact coordinates_golden (icosahedralRaw i) j

theorem standardPoint_axis (i : Fin 4) : standardPoint (axis i) = Pi.single i 1 := by
  fin_cases i <;> funext j <;> fin_cases j <;>
    norm_num [standardPoint_literal,axis,icosahedralRaw,
      GoldenInt.eval,Pi.single_apply]

theorem standardPoint_four : standardPoint 4 = ![1,1,1,1] := by
  funext i
  fin_cases i <;> norm_num [standardPoint_literal,
    icosahedralRaw,GoldenInt.eval]

theorem standardPoint_seven : standardPoint 7 = ![1,1,-1,-1] := by
  funext i
  fin_cases i <;> norm_num [standardPoint_literal,
    icosahedralRaw,GoldenInt.eval]

theorem standardPoint_nine : standardPoint 9 = ![1,-1,1,-1] := by
  funext i
  fin_cases i <;> norm_num [standardPoint_literal,
    icosahedralRaw,GoldenInt.eval]

theorem standardPoint_ten : standardPoint 10 = ![1,-1,-1,1] := by
  funext i
  fin_cases i <;> norm_num [standardPoint_literal,
    icosahedralRaw,GoldenInt.eval]

def pulledLinear (opposite : Bool) (A : End) : V →ₗ[ℂ] V :=
  (frame opposite).symm.toLinearMap.comp
    (A.mulVecLin.comp (frame opposite).toLinearMap)

def pulledMatrix (opposite : Bool) (A : End) : End := LinearMap.toMatrix' (pulledLinear opposite A)

theorem pulled_action (opposite : Bool) (A : End) (v : V) :
    pulledMatrix opposite A *ᵥ v = (frame opposite).symm (A *ᵥ frame opposite v) :=
  LinearMap.toMatrix'_mulVec (pulledLinear opposite A) v

theorem pulled_point (opposite : Bool) (A : End) (i : Fin 60) :
    pulledMatrix opposite A *ᵥ standardPoint i = (frame opposite).symm (A *ᵥ point opposite i) := by
  rw [pulled_action,←point_frame]

def gram (B : End) : End := B.transpose * B

theorem polar_gram (B : End) (u v : V) :
    polar (B *ᵥ u) (B *ᵥ v) = polar u (gram B *ᵥ v) := by
  change (B *ᵥ u) ⬝ᵥ (B *ᵥ v) = u ⬝ᵥ ((B.transpose*B) *ᵥ v)
  rw [←Matrix.mulVec_mulVec]
  exact (dotProduct_comm _ _).trans
    (Matrix.dotProduct_transpose_mulVec B u (B *ᵥ v)).symm

theorem gram_axis (B : End) (i j : Fin 4) :
    polar (B *ᵥ Pi.single i 1) (B *ᵥ Pi.single j 1) = gram B i j := by
  rw [polar_gram]
  change Pi.single i 1 ⬝ᵥ (gram B *ᵥ Pi.single j 1) = _
  simp only [Matrix.mulVec_single_one,single_dotProduct,one_mul,Matrix.col,Matrix.transpose_apply]

theorem gram_points (opposite : Bool) (A : End) (i j : Fin 60) :
    polar (standardPoint i) (gram (pulledMatrix opposite A) *ᵥ standardPoint j) =
      rowPolar opposite (A *ᵥ point opposite i) (A *ᵥ point opposite j) := by
  rw [←polar_gram]
  simp only [pulled_point,rowPolar]

theorem gram_conformal_of_action (opposite : Bool) (A : End) (hA : A.det ≠ 0)
    (σ : Equiv.Perm (Fin 60)) (c : Fin 60 → ℂ) (hc : ∀ i,c i ≠ 0)
    (he : ∀ i,A *ᵥ point opposite i = c i • point opposite (σ i)) :
    ∃ lam : ℂ, lam ≠ 0 ∧ gram (pulledMatrix opposite A) = lam • (1 : End) := by
  let B := pulledMatrix opposite A
  let G := gram B
  have offdiag (i j : Fin 4) (hij : i ≠ j) : G i j = 0 := by
    have hne : axis i ≠ axis j := fun h => hij (axis_injective h)
    have hz : rowPolar opposite (point opposite (axis i)) (point opposite (axis j))=0 := by
      simp only [rowPolar_point,standardPoint_axis]
      change Pi.single i (1 : ℂ) ⬝ᵥ Pi.single j 1 = 0
      simp [single_dotProduct,Pi.single_apply,hij,hij.symm]
    have hm := action_orthogonal opposite A hA σ c hc he (axis i) (axis j) hne hz
    rw [←gram_points] at hm
    simp only [standardPoint_axis] at hm
    change Pi.single i (1 : ℂ) ⬝ᵥ (G *ᵥ Pi.single j 1) = 0 at hm
    simpa only [Matrix.mulVec_single_one,single_dotProduct,one_mul,Matrix.col,Matrix.transpose_apply] using hm
  have hG : G = Matrix.diagonal (fun i => G i i) := by
    ext i j
    by_cases hij : i=j
    · subst j
      simp [Matrix.diagonal_apply]
    · simp only [Matrix.diagonal_apply,if_neg hij,offdiag i j hij]
  have h7 : G 0 0 + G 1 1 - G 2 2 - G 3 3=0 := by
    have hz : rowPolar opposite (point opposite 4) (point opposite 7)=0 := by
      rw [rowPolar_point,standardPoint_four,standardPoint_seven]
      norm_num [polar,Fin.sum_univ_four]
    have hm := action_orthogonal opposite A hA σ c hc he 4 7 (by decide) hz
    rw [←gram_points] at hm
    change polar (standardPoint 4) (G *ᵥ standardPoint 7)=0 at hm
    rw [hG] at hm
    simpa [polar,Fin.sum_univ_four,standardPoint_four,standardPoint_seven,
      Matrix.mulVec_diagonal,sub_eq_add_neg] using hm
  have h9 : G 0 0 - G 1 1 + G 2 2 - G 3 3=0 := by
    have hz : rowPolar opposite (point opposite 4) (point opposite 9)=0 := by
      rw [rowPolar_point,standardPoint_four,standardPoint_nine]
      norm_num [polar,Fin.sum_univ_four]
    have hm := action_orthogonal opposite A hA σ c hc he 4 9 (by decide) hz
    rw [←gram_points] at hm
    change polar (standardPoint 4) (G *ᵥ standardPoint 9)=0 at hm
    rw [hG] at hm
    simpa [polar,Fin.sum_univ_four,standardPoint_four,standardPoint_nine,
      Matrix.mulVec_diagonal,sub_eq_add_neg] using hm
  have h10 : G 0 0 - G 1 1 - G 2 2 + G 3 3=0 := by
    have hz : rowPolar opposite (point opposite 4) (point opposite 10)=0 := by
      rw [rowPolar_point,standardPoint_four,standardPoint_ten]
      norm_num [polar,Fin.sum_univ_four]
    have hm := action_orthogonal opposite A hA σ c hc he 4 10 (by decide) hz
    rw [←gram_points] at hm
    change polar (standardPoint 4) (G *ᵥ standardPoint 10)=0 at hm
    rw [hG] at hm
    simpa [polar,Fin.sum_univ_four,standardPoint_four,standardPoint_ten,
      Matrix.mulVec_diagonal,sub_eq_add_neg] using hm
  have hd1 : G 1 1=G 0 0 := by
    linear_combination (-1/2 : ℂ)*h9 + (-1/2 : ℂ)*h10
  have hd2 : G 2 2=G 0 0 := by
    linear_combination (-1/2 : ℂ)*h7 + (-1/2 : ℂ)*h10
  have hd3 : G 3 3=G 0 0 := by
    linear_combination (-1/2 : ℂ)*h7 + (-1/2 : ℂ)*h9
  have diagonal (i : Fin 4) : G i i=G 0 0 := by
    fin_cases i
    · rfl
    · exact hd1
    · exact hd2
    · exact hd3
  have hscale : G 0 0 = (c 0*c 0) * (representative .icosahedral (σ 0)).det := by
    have hh := gram_points opposite A (axis 0) (axis 0)
    simp only [standardPoint_axis] at hh
    have hh' : G 0 0 = rowPolar opposite (A *ᵥ point opposite 0) (A *ᵥ point opposite 0) := by
      change Pi.single (0 : Fin 4) (1 : ℂ) ⬝ᵥ (G *ᵥ Pi.single 0 1) =
        rowPolar opposite (A *ᵥ point opposite 0) (A *ᵥ point opposite 0) at hh
      simpa only [Matrix.mulVec_single_one,single_dotProduct,one_mul,Matrix.col,Matrix.transpose_apply] using hh
    rw [hh']
    simp only [he 0,rowPolar_smul,rowPolar_point,standardPoint,←determinant_polar]
  have hnonzero : G 0 0 ≠ 0 := by
    rw [hscale]
    exact mul_ne_zero (mul_ne_zero (hc 0) (hc 0)) (representative_det_ne_zero .icosahedral _)
  refine ⟨G 0 0,hnonzero,?_⟩
  change G = G 0 0 • (1 : End)
  ext i j
  simp only [Matrix.smul_apply,smul_eq_mul,Matrix.one_apply]
  by_cases hij : i=j
  · subst j
    simp [diagonal]
  · simp only [if_neg hij,mul_zero,offdiag i j hij]

/-- Only the original one-sided root condition and invertibility are
inputs. The root permutation and every Gram premise are PRODUCED inside. -/
theorem gram_conformal (opposite : Bool) (A : End) (hA : A.det ≠ 0)
    (h : OneSided (Preserver.roots opposite) A) :
    ∃ lam : ℂ, lam ≠ 0 ∧ gram (pulledMatrix opposite A) = lam • (1 : End) := by
  obtain ⟨σ,c,hc,he⟩ := invertible_permutation opposite A hA h
  exact gram_conformal_of_action opposite A hA σ c hc he

/-- The SAME original map, pulled through the exact literal coefficient
dictionary, is a linear map on the ORIGINAL Bool×Bool matrix space. -/
def binaryMap (opposite : Bool) (A : End) : Matrix Bool Bool ℂ →ₗ[ℂ] Matrix Bool Bool ℂ :=
  coordinates.symm.toLinearMap.comp ((pulledLinear opposite A).comp coordinates.toLinearMap)

theorem binaryMap_coordinates (opposite : Bool) (A : End) (K : Matrix Bool Bool ℂ) :
    coordinates (binaryMap opposite A K) = pulledMatrix opposite A *ᵥ coordinates K := by
  rw [pulled_action]
  exact coordinates.apply_symm_apply _

theorem binaryMap_injective (opposite : Bool) (A : End) (hA : A.det ≠ 0) :
    Function.Injective (binaryMap opposite A) := by
  intro K W h
  apply coordinates.injective
  apply (frame opposite).injective
  apply Matrix.mulVec_injective_of_det_ne_zero hA
  apply (frame opposite).symm.injective
  exact coordinates.symm.injective h

/-- Exact interface to the independent Segre/rulings producer. The
determinant multiplier is derived from the actual H4 equations, not given
as a scalar, optimizer, permutation catalogue, or desired normal form. -/
theorem binaryMap_determinant (opposite : Bool) (A : End) (hA : A.det ≠ 0)
    (h : OneSided (Preserver.roots opposite) A) :
    ∃ lam : ℂ, lam ≠ 0 ∧ ∀ K : Matrix Bool Bool ℂ,
      (binaryMap opposite A K).det = lam*K.det := by
  obtain ⟨lam,hlam,hgram⟩ := gram_conformal opposite A hA h
  refine ⟨lam,hlam,?_⟩
  intro K
  rw [determinant_polar,binaryMap_coordinates,polar_gram,hgram,
    Matrix.smul_mulVec,Matrix.one_mulVec,polar_smul_right,←determinant_polar]

/-- Original current-coordinate binary coefficient operator. In
particular this definition contains no kappa, D, chart or selected root. -/
def actualBinaryMap (A : End) : Matrix Bool Bool ℂ →ₗ[ℂ] Matrix Bool Bool ℂ :=
  coordinates.symm.toLinearMap.comp (A.mulVecLin.comp coordinates.toLinearMap)

theorem actualBinaryMap_coordinates (A : End) (K : Matrix Bool Bool ℂ) :
    coordinates (actualBinaryMap A K) = A *ᵥ coordinates K :=
  coordinates.apply_symm_apply _

theorem actualBinaryMap_injective (A : End) (hA : A.det ≠ 0) :
    Function.Injective (actualBinaryMap A) := by
  intro K W h
  apply coordinates.injective
  apply Matrix.mulVec_injective_of_det_ne_zero hA
  exact coordinates.symm.injective h

theorem actualBinaryMap_preserves (opposite : Bool) (A : End) (hA : A.det ≠ 0)
    (h : OneSided (Preserver.roots opposite) A) (K : Matrix Bool Bool ℂ)
    (hK : Dictionary.direction opposite K) :
    Dictionary.direction opposite (actualBinaryMap A K) := by
  have hroot : coordinates K ∈ Preserver.roots opposite := ⟨K,hK,rfl⟩
  rcases h _ hroot with hz | hm
  · have hzero : coordinates K=0 :=
      Matrix.mulVec_injective_of_det_ne_zero hA (by simpa using hz)
    have hKzero : K=0 := coordinates.injective (by simpa using hzero)
    exact False.elim (direction_ne_zero opposite hK hKzero)
  · have hc : coordinates (actualBinaryMap A K) ∈ Preserver.roots opposite := by
      rw [actualBinaryMap_coordinates]
      exact hm
    obtain ⟨W,hW,he⟩ := hc
    exact (coordinates.injective he) ▸ hW

private theorem opposite_pull_actual (A : End) (K : Matrix Bool Bool ℂ) :
    binaryMap true A (OppositeIcosahedral.unkappa K) =
      OppositeIcosahedral.unkappa (actualBinaryMap A K) := by
  change coordinates.symm ((frame true).symm
    (A *ᵥ frame true (coordinates (OppositeIcosahedral.unkappa K))))=
      OppositeIcosahedral.unkappa (coordinates.symm (A *ᵥ coordinates K))
  have hf : frame true (coordinates (OppositeIcosahedral.unkappa K))=coordinates K := by
    change coordinates (OppositeIcosahedral.kappa (coordinates.symm
      (coordinates (OppositeIcosahedral.unkappa K))))=coordinates K
    rw [coordinates.symm_apply_apply,OppositeIcosahedral.kappa_unkappa]
  rw [hf]
  change coordinates.symm (coordinates
    (OppositeIcosahedral.unkappa (coordinates.symm (A *ᵥ coordinates K))))=_
  exact coordinates.symm_apply_apply _

private theorem unkappa_determinant (K : Matrix Bool Bool ℂ) :
    (OppositeIcosahedral.unkappa K).det = (4 : ℂ)*K.det := by
  simp only [OppositeIcosahedral.unkappa,Matrix.det_mul,Matrix.det_transpose,
    OppositeIcosahedral.D_det]
  ring

/-- The multiplier is the SAME lam, also on the original current matrix
operator. The opposite chart's determinant factor four is cancelled on
BOTH sides; it is not installed as a physical binary. -/
theorem actualBinaryMap_determinant (opposite : Bool) (A : End) (hA : A.det ≠ 0)
    (h : OneSided (Preserver.roots opposite) A) :
    ∃ lam : ℂ, lam ≠ 0 ∧ ∀ K : Matrix Bool Bool ℂ,
      (actualBinaryMap A K).det = lam*K.det := by
  obtain ⟨lam,hlam,hdet⟩ := binaryMap_determinant opposite A hA h
  refine ⟨lam,hlam,?_⟩
  intro K
  cases opposite
  · exact hdet K
  · have ht := hdet (OppositeIcosahedral.unkappa K)
    rw [opposite_pull_actual] at ht
    simp only [unkappa_determinant] at ht
    apply mul_left_cancel₀ (by norm_num : (4 : ℂ) ≠ 0)
    calc
      (4 : ℂ)*(actualBinaryMap A K).det = lam*((4 : ℂ)*K.det) := ht
      _ = 4*(lam*K.det) := by ring

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIcosahedral.RankFour
end
