import Holant.Proofs.Dichotomy.Retained.StableDenseResidualGaugeCore
import Holant.Tractable.AffinePhase.Roots
import Holant.Tractable.Conformal.MatrixSupport

/-! A simultaneous positive branch for weighted-even rows. A single nonzero
parameter t is shared by every row and every port. The actual diagonal basis
diag(1,t) makes all rows affine and pulls the mandatory native X edge back to
t*X. This does not assign independently chosen bases to separate rows. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EightVertexGaugeAffine
open Holant Holant.Tractable
open Holant.LocalDrafts.Hardness.EightVertexNonexception
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1
open StableDenseResidualGaugeCore
open scoped BigOperators

def evenSystem : AffineSystem 4 := ⟨1,fun _ _ => 1,fun _ => 0⟩

theorem evenSystem_holds (x : Fin 4 → Bool) : evenSystem.Holds x ↔ weight x % 2 = 0 := by
  rw [word_eta x]
  cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;> decide

def linearPhase (q : Fin 4 → ZMod 4) : QuadraticPhase 4 :=
  ⟨0,q,fun _ _ => 0,fun _ _ _ => Or.inl rfl⟩

theorem linearPhase_value (q : Fin 4 → ZMod 4) (x : Fin 4 → Bool) :
    fourthRootPhase ((linearPhase q).eval x) =
      ∏ i, if x i then fourthRootPhase (q i) else 1 := by
  simp only [linearPhase,QuadraticPhase.eval,zero_mul,ite_self,
    Finset.sum_const_zero,zero_add,add_zero]
  rw [fourthRootPhase_sum]
  apply Finset.prod_congr rfl
  intro i _
  cases x i <;> simp [bitValue]

/-- Independent fourth-root port phases are a genuine linear affine phase. -/
theorem weighted_affine (a : AlgebraicComplex) (u : Fin 4 → AlgebraicComplex)
    (roots : ∀ i, u i ^ 4 = 1) : Affine (weighted a u) := by
  have codes : ∀ i, ∃ q : ZMod 4, fourthRootPhase q = u i :=
    fun i => fourthRootPhase_surjective_of_pow_four (roots i)
  choose q hq using codes
  convert affine_formula a evenSystem (linearPhase q) using 1
  funext x
  rw [weighted_value]
  simp only [affineFormula,evenSystem_holds,linearPhase_value,hq]

def diagonalBasis (t : AlgebraicComplex) (ht : t ≠ 0) : InvertibleKernel where
  matrix := diagonalKernel 1 t
  inverse := diagonalKernel 1 t⁻¹
  matrix_inverse := by
    funext x y
    cases x <;> cases y <;>
      simp [diagonalKernel,Kernel.mul_apply,Signature.equality,ht]
  inverse_matrix := by
    funext x y
    cases x <;> cases y <;>
      simp [diagonalKernel,Kernel.mul_apply,Signature.equality,ht]

theorem diagonal_action (t : AlgebraicComplex) (ht : t ≠ 0)
    (a : AlgebraicComplex) (u : Fin 4 → AlgebraicComplex) :
    (diagonalBasis t ht).symm.action (weighted a u) = weighted a (fun i => u i/t) := by
  change Signature.coordinateAction (fun _ => diagonalKernel 1 t⁻¹) (weighted a u) = _
  rw [coordinateAction_diagonal]
  funext x
  rw [word_eta x]
  cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;>
    simp [weighted,table,diagonalCoefficient,Fin.prod_univ_four,div_eq_mul_inv] <;> ring

theorem diagonal_edge (t : AlgebraicComplex) (ht : t ≠ 0) :
    Kernel.pullback Signature.disequality (diagonalBasis t ht).matrix =
      fun x y => t * Signature.disequality x y := by
  funext x y
  cases x <;> cases y <;>
    simp [diagonalBasis,Kernel.pullback,Kernel.mul_apply,Kernel.transpose_apply,
      diagonalKernel,Signature.disequality]

private theorem edge_affine : Affine (kernelSignature
    (Signature.disequality : Kernel AlgebraicComplex)) := by
  let S : AffineSystem 2 := ⟨1,fun _ _ => 1,fun _ => 1⟩
  have holds (x : Fin 2 → Bool) : S.Holds x ↔ x 0 ≠ x 1 := by
    change (∀ _ : Fin 1, (∑ j : Fin 2, (1 : ZMod 2)*bitValue (ZMod 2) (x j)) = 1) ↔ _
    simp only [Fin.forall_fin_one,Fin.sum_univ_two,one_mul]
    cases x 0 <;> cases x 1 <;> decide
  convert affine_indicator S using 1
  funext x
  change Signature.disequality (x 0) (x 1) = if S.Holds x then 1 else 0
  simp only [holds]
  cases x 0 <;> cases x 1 <;> rfl

/-- Every row here uses the SAME parameter t. There is no per-row existential
outside the family condition and the original scale a remains arbitrary. -/
def family (t : AlgebraicComplex) : SignatureFamily AlgebraicComplex :=
  {f | ∃ (a : AlgebraicComplex) (u : Fin 4 → AlgebraicComplex),
    f = ⟨4,weighted a u⟩ ∧ ∀ i, u i ^ 4 = t ^ 4}

theorem common_affine_basis (t : AlgebraicComplex) (ht : t ≠ 0) :
    IsCommonKBasis affineClass (family t) (diagonalBasis t ht) := by
  constructor
  · change Affine (kernelSignature (Kernel.pullback Signature.disequality
      (diagonalBasis t ht).matrix))
    rw [diagonal_edge]
    exact edge_affine.scale t
  · rintro f ⟨a,u,rfl,hpow⟩
    change Affine ((diagonalBasis t ht).symm.action (weighted a u))
    rw [diagonal_action]
    apply weighted_affine
    intro i
    rw [div_pow,hpow i]
    exact div_self (pow_ne_zero 4 ht)

/-- Restriction to an actual supplied family retains both the single basis
and its native edge obligation. This does not classify other current leaves. -/
theorem common_affine_subfamily (F : SignatureFamily AlgebraicComplex)
    (t : AlgebraicComplex) (ht : t ≠ 0) (members : F ⊆ family t) :
    IsCommonKBasis affineClass F (diagonalBasis t ht) := by
  have h := common_affine_basis t ht
  exact ⟨h.1,fun f hf => h.2 f (members hf)⟩

/-- The row conclusion uses its original port zero as one shared anchor.
All four coordinates and the native edge use this exact same basis. -/
theorem singleton_basis_of_fourths (a : AlgebraicComplex) (u : Fin 4 → AlgebraicComplex)
    (hu0 : u 0 ≠ 0) (same : ∀ i, u i ^ 4 = u 0 ^ 4) :
    IsCommonKBasis affineClass {⟨4,weighted a u⟩} (diagonalBasis (u 0) hu0) := by
  apply common_affine_subfamily _ (u 0) hu0
  intro f hf
  rcases Set.mem_singleton_iff.mp hf with rfl
  exact ⟨a,u,rfl,same⟩

private theorem affine_diagonal_root (r : AlgebraicComplex) (hr : r ^ 4 = 1) :
    Affine (kernelSignature (diagonalKernel 1 r)) := by
  obtain ⟨q,hq⟩ := fourthRootPhase_surjective_of_pow_four hr
  let S : AffineSystem 2 := ⟨1,fun _ _ => 1,fun _ => 0⟩
  let Q : QuadraticPhase 2 := ⟨0,![q,0],fun _ _ => 0,fun _ _ _ => Or.inl rfl⟩
  have holds (x : Fin 2 → Bool) : S.Holds x ↔ x 0 = x 1 := by
    change (∀ _ : Fin 1, (∑ j : Fin 2, (1 : ZMod 2)*bitValue (ZMod 2) (x j)) = 0) ↔ _
    simp only [Fin.forall_fin_one,Fin.sum_univ_two,one_mul]
    cases x 0 <;> cases x 1 <;> decide
  convert affine_formula 1 S Q using 1
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;>
    simp [kernelSignature,diagonalKernel,affineFormula,holds,h0,h1,Q,
      QuadraticPhase.eval,Fin.sum_univ_two,bitValue,hq]

/-- I is a supplied vertex, so it uses the inverse action, whereas the
native X edge uses the pullback already proved in diagonal_edge. -/
theorem identity_action (t : AlgebraicComplex) (ht : t ≠ 0) :
    (diagonalBasis t ht).symm.action (kernelSignature Signature.equality) =
      kernelSignature (diagonalKernel 1 ((t⁻¹)^2)) := by
  change Signature.coordinateAction (fun _ => diagonalKernel 1 t⁻¹)
    (kernelSignature Signature.equality) = _
  rw [coordinateAction_diagonal]
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;>
    simp [kernelSignature,diagonalKernel,diagonalCoefficient,Fin.prod_univ_two,
      Signature.equality,h0,h1,pow_two]

theorem identity_affine_of_eighth (t : AlgebraicComplex) (ht : t ≠ 0) (h8 : t ^ 8 = 1) :
    Affine ((diagonalBasis t ht).symm.action (kernelSignature Signature.equality)) := by
  rw [identity_action]
  apply affine_diagonal_root
  simp [← pow_mul,inv_pow,h8]

/-- One basis handles the original row, its retained I vertex, and native X.
The eighth-root condition is explicit until forced by the two-I physical test. -/
theorem row_identity_basis (a : AlgebraicComplex) (u : Fin 4 → AlgebraicComplex)
    (hu0 : u 0 ≠ 0) (same : ∀ i, u i ^ 4 = u 0 ^ 4) (h8 : u 0 ^ 8 = 1) :
    IsCommonKBasis affineClass
      {⟨4,weighted a u⟩,⟨2,kernelSignature Signature.equality⟩}
      (diagonalBasis (u 0) hu0) := by
  have single := singleton_basis_of_fourths a u hu0 same
  refine ⟨single.1,?_⟩
  intro f hf
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hf
  rcases hf with rfl | rfl
  · exact single.2 _ (Set.mem_singleton _)
  · exact identity_affine_of_eighth (u 0) hu0 h8

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EightVertexGaugeAffine
end
