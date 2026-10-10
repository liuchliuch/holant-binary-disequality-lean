import Holant.ReedMuller.FlatNetwork.GenerationReduction
import Mathlib.Data.Matrix.Mul

/-! Literal orthogonal coordinate maps for source Lemma 7.15.  The reducing
program acts on the given word itself, with an exact number of weight-four
gates; its matrix and transpose are the actual standard-coordinate matrices. -/
namespace Holant.ReedMuller.RadonAccess
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

def unitWord (i : Fin n) : BinaryVector n := Pi.single i 1

@[simp] theorem unitWord_apply (i j : Fin n) : unitWord i j = if j = i then 1 else 0 := by
  simp [unitWord, Pi.single_apply, eq_comm]

@[simp] theorem dot_unit_right (x : BinaryVector n) (i : Fin n) : dot x (unitWord i) = x i := by
  simp [dot, unitWord_apply]

@[simp] theorem dot_unit_left (x : BinaryVector n) (i : Fin n) : dot (unitWord i) x = x i := by
  rw [dot_comm, dot_unit_right]

theorem dot_ext {x y : BinaryVector n} (h : ∀ z, dot x z = dot y z) : x = y := by
  funext i
  simpa using h (unitWord i)

/-- An actual invertible linear coordinate map preserving the binary dot product. -/
structure OrthogonalMap (n : ℕ) where
  linear : BinaryVector n ≃ₗ[ZMod 2] BinaryVector n
  isometry : ∀ x y, dot (linear x) (linear y) = dot x y

namespace OrthogonalMap
instance : CoeFun (OrthogonalMap n) (fun _ => BinaryVector n → BinaryVector n) :=
  ⟨fun A => A.linear⟩

def symm (A : OrthogonalMap n) : OrthogonalMap n where
  linear := A.linear.symm
  isometry := by
    intro x y
    have h := A.isometry (A.linear.symm x) (A.linear.symm y)
    simpa using h.symm

@[simp] theorem symm_apply_apply (A : OrthogonalMap n) (x : BinaryVector n) : A.symm (A x) = x :=
  A.linear.symm_apply_apply x
@[simp] theorem apply_symm_apply (A : OrthogonalMap n) (x : BinaryVector n) : A (A.symm x) = x :=
  A.linear.apply_symm_apply x
@[simp] theorem map_zero (A : OrthogonalMap n) : A 0 = 0 := A.linear.map_zero
@[simp] theorem map_add (A : OrthogonalMap n) (x y : BinaryVector n) : A (x+y) = A x+A y :=
  A.linear.map_add x y
@[simp] theorem map_smul (A : OrthogonalMap n) (c : ZMod 2) (x : BinaryVector n) :
    A (c • x) = c • A x := A.linear.map_smul c x

theorem adjoint (A : OrthogonalMap n) (x y : BinaryVector n) :
    dot (A x) y = dot x (A.symm y) := by
  rw [← A.isometry x (A.symm y), apply_symm_apply]

theorem fixes_ones (A : OrthogonalMap n) : A (ones n) = ones n := by
  apply dot_ext
  intro z
  obtain ⟨x, rfl⟩ := A.linear.surjective z
  rw [A.isometry, dot_ones, dot_ones, A.isometry]

/-- Entries are obtained by applying the map to literal standard basis words. -/
def matrix (A : OrthogonalMap n) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  fun i j => A (unitWord j) i

/-- The displayed matrix has precisely the given coordinate action. -/
theorem matrix_mulVec (A : OrthogonalMap n) (x : BinaryVector n) : A.matrix.mulVec x = A x := by
  have hx : x = ∑ j, x j • unitWord j := by
    funext i
    simp [unitWord_apply]
  conv_rhs => rw [hx]
  change _ = A.linear (∑ j, x j • unitWord j)
  rw [map_sum]
  simp only [map_smul]
  funext i
  simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, matrix]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

/-- The transpose is the inverse map, proved coordinate by coordinate. -/
theorem transpose_mulVec (A : OrthogonalMap n) (x : BinaryVector n) :
    A.matrix.transpose.mulVec x = A.symm x := by
  funext i
  change dot (A (unitWord i)) x = _
  rw [A.adjoint, dot_unit_left]

/-- Thus this is literally an element of the matrix orthogonal group. -/
theorem transpose_mul (A : OrthogonalMap n) : A.matrix.transpose * A.matrix = 1 := by
  ext i j
  change dot (A (unitWord i)) (A (unitWord j)) = _
  rw [A.isometry, dot_unit_left]
  simp [unitWord_apply, Matrix.one_apply]

/-- The recorded transpose is both a left and a right inverse of the matrix. -/
theorem mul_transpose (A : OrthogonalMap n) : A.matrix * A.matrix.transpose = 1 := by
  ext i j
  have h : (A.matrix*A.matrix.transpose).mulVec (unitWord j) = unitWord j := by
    rw [←Matrix.mulVec_mulVec,A.transpose_mulVec,A.matrix_mulVec,A.apply_symm_apply]
  have hh := congrFun h i
  simpa [Matrix.mulVec,dotProduct,unitWord_apply,Matrix.one_apply] using hh

end OrthogonalMap

end
end Holant.ReedMuller.RadonAccess

namespace Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.LowArity Holant.ReedMuller.RadonAccess
noncomputable section
variable {n : ℕ}

namespace GenerationGate

def linear (g : GenerationGate n) : BinaryVector n →ₗ[ZMod 2] BinaryVector n :=
  match g with
  | .tau s _ => transvectionLinear s
  | .perm e => coordinateMap e.symm

@[simp] theorem linear_apply (g : GenerationGate n) (x : BinaryVector n) :
    g.linear x = g.applyWord x := by cases g <;> rfl

theorem word_isometry (g : GenerationGate n) (x y : BinaryVector n) :
    dot (g.applyWord x) (g.applyWord y) = dot x y := by
  cases g with
  | tau s hs => exact transvection_isometry s (GenerationGate.weightFour_isotropic s hs) x y
  | perm e => exact dot_coordinateMap e.symm x y

end GenerationGate

namespace GenerationProgram

def linear : GenerationProgram n → BinaryVector n →ₗ[ZMod 2] BinaryVector n
  | [] => LinearMap.id
  | g :: p => g.linear.comp (linear p)

@[simp] theorem linear_apply (p : GenerationProgram n) (x : BinaryVector n) :
    p.linear x = p.word x := by
  induction p with
  | nil => rfl
  | cons g p ih => change g.linear (linear p x) = _; rw [ih, GenerationGate.linear_apply]; rfl

theorem word_isometry (p : GenerationProgram n) (x y : BinaryVector n) :
    dot (p.word x) (p.word y) = dot x y := by
  induction p with
  | nil => rfl
  | cons g p ih => exact (g.word_isometry (word p x) (word p y)).trans ih

def orthogonalMap (p : GenerationProgram n) : OrthogonalMap n where
  linear := LinearEquiv.ofBijective p.linear (by
    change Function.Bijective (fun x => p.linear x)
    simpa only [linear_apply] using p.word_bijective)
  isometry := by
    intro x y
    change dot (p.linear x) (p.linear y) = dot x y
    simpa only [linear_apply] using p.word_isometry x y

@[simp] theorem orthogonalMap_apply (p : GenerationProgram n) (x : BinaryVector n) :
    p.orthogonalMap x = p.word x := linear_apply p x

/-- The orthogonal inverse agrees with the actual reversed generation program. -/
@[simp] theorem orthogonalMap_symm_apply (p : GenerationProgram n) (x : BinaryVector n) :
    p.orthogonalMap.symm x = p.inverse.word x := by
  apply p.orthogonalMap.linear.injective
  rw [OrthogonalMap.apply_symm_apply,orthogonalMap_apply]
  symm
  simpa only [inverse_inverse] using word_inverse p.inverse x

end GenerationProgram
end
end Holant.ReedMuller.FlatNetwork

namespace Holant.ReedMuller.RadonAccess
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

/-- Exactly the source's even, nonzero, non-all-one directions. -/
def Accessible (v : BinaryVector n) : Prop := dot (ones n) v = 0 ∧ v ≠ 0 ∧ v ≠ ones n

private theorem reduceWordAux (w : ℕ) :
    ∀ x : BinaryVector n, dot x x = 0 → binaryWeight x = w → 0 < w → w < n →
      ∃ p : GenerationProgram n, 2*p.length+2 = w ∧ binaryWeight (p.word x) = 2 := by
  induction w using Nat.strong_induction_on with
  | h w ih =>
    intro x his hw hp hz
    by_cases htwo : w = 2
    · exact ⟨[], by simp [htwo], hw.trans htwo⟩
    have he : Even w := by
      apply even_iff_two_dvd.mpr
      apply (ZMod.natCast_eq_zero_iff w 2).mp
      rw [← hw, cast_binaryWeight, his]
    obtain ⟨a, ha⟩ := he
    obtain ⟨s, hs, hss, hdrop⟩ := exists_weightFour_reduction x (by omega) (by omega)
    have hsmall : binaryWeight (transvection s x) < w := by omega
    obtain ⟨p, hlen, hwt⟩ := ih _ hsmall (transvection s x)
      (by rw [transvection_isometry s hss, his]) rfl (by omega) (by omega)
    refine ⟨p ++ [.tau s hs], ?_, ?_⟩
    · simp only [List.length_append, List.length_singleton]; omega
    · simpa only [GenerationProgram.word_append, GenerationProgram.word,
        GenerationGate.applyWord] using hwt

/-- The map is built from exactly `(weight(v)-2)/2` genuine weight-four gates.
No self-dual-code membership hypothesis is needed. -/
theorem accessible_reduction (v : BinaryVector n) (hv : Accessible v) :
    ∃ p : GenerationProgram n, 2*p.length+2 = binaryWeight v ∧
      binaryWeight (p.word v) = 2 := by
  exact reduceWordAux (binaryWeight v) v (by simpa only [dot_ones] using hv.1) rfl
    ((binaryWeight_pos_iff v).mpr hv.2.1) ((binaryWeight_lt_iff v).mpr hv.2.2)

theorem supportWord_pair (i j : Fin n) (hij : i ≠ j) :
    supportWord {i,j} = unitWord i + unitWord j := by
  funext k
  by_cases hki : k = i
  · subst k; simp [supportWord, unitWord_apply, hij]
  · by_cases hkj : k = j
    · subst k; simp [supportWord, unitWord_apply, hki]
    · simp [supportWord, unitWord_apply, hki, hkj]

theorem weight_pair (i j : Fin n) (hij : i ≠ j) : binaryWeight (unitWord i + unitWord j) = 2 := by
  rw [← supportWord_pair i j hij, binaryWeight_supportWord]
  simp [hij]

theorem exists_ports_of_weight_two (x : BinaryVector n) (hx : binaryWeight x = 2) :
    ∃ i j : Fin n, i ≠ j ∧ x = unitWord i + unitWord j := by
  obtain ⟨i,j,hij,hs⟩ := Finset.card_eq_two.mp (show (wordSupport x).card = 2 from hx)
  refine ⟨i,j,hij,?_⟩
  rw [← supportWord_wordSupport x, hs, supportWord_pair i j hij]

/-- Constructive sufficiency with an actual program, coordinate map, matrix,
transpose equation, distinct physical ports, and a linear gate bound. -/
theorem accessible_coordinate_map (v : BinaryVector n) (hv : Accessible v) :
    ∃ (p : GenerationProgram n) (i j : Fin n), i ≠ j ∧
      2*p.length+2 = binaryWeight v ∧ p.length ≤ n ∧
      p.orthogonalMap v = unitWord i + unitWord j ∧
      p.orthogonalMap.matrix.transpose.mulVec (unitWord i + unitWord j) = v := by
  obtain ⟨p,hlen,hwt⟩ := accessible_reduction v hv
  obtain ⟨i,j,hij,hijv⟩ := exists_ports_of_weight_two _ hwt
  refine ⟨p,i,j,hij,hlen,?_,by simpa using hijv,?_⟩
  · have hle := binaryWeight_le v; omega
  · rw [OrthogonalMap.transpose_mulVec, ← hijv]
    simpa only [GenerationProgram.orthogonalMap_apply] using p.orthogonalMap.symm_apply_apply v

/-- Necessity is for arbitrary orthogonal linear maps, not merely the maps
produced by the reduction algorithm. -/
theorem accessible_of_pair_image (hn : 4 ≤ n) (A : OrthogonalMap n)
    (v : BinaryVector n) (i j : Fin n) (hij : i ≠ j)
    (hv : A v = unitWord i + unitWord j) : Accessible v := by
  have hwt := weight_pair i j hij
  have his : dot v v = 0 := by
    rw [← A.isometry, hv, ← cast_binaryWeight, hwt]
    decide
  refine ⟨by rwa [dot_ones], ?_, ?_⟩
  · intro hz
    have h : unitWord i + unitWord j = 0 := by rw [← hv, hz, A.map_zero]
    rw [h] at hwt
    simp [binaryWeight] at hwt
  · intro ho
    have h : unitWord i + unitWord j = ones n := by rw [← hv, ho, A.fixes_ones]
    rw [h] at hwt
    have hweight : binaryWeight (ones n) = n := by simp [binaryWeight, ones]
    omega

/-- The available directions are exactly the displayed source vectors. -/
theorem accessible_iff_orthogonal_pair (hn : 4 ≤ n) (v : BinaryVector n) :
    Accessible v ↔ ∃ (A : OrthogonalMap n) (i j : Fin n),
      i ≠ j ∧ A v = unitWord i + unitWord j := by
  constructor
  · intro hv
    obtain ⟨p,i,j,hij,_,_,h,_⟩ := accessible_coordinate_map v hv
    exact ⟨p.orthogonalMap,i,j,hij,h⟩
  · rintro ⟨A,i,j,hij,hv⟩
    exact accessible_of_pair_image hn A v i j hij hv

end
end Holant.ReedMuller.RadonAccess
