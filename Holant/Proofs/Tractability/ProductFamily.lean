import Holant.Proofs.Tractability.ProductNetwork
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.GraphListCompiler
import Holant.Holographic


set_option backward.isDefEq.respectTransparency false

namespace Holant.LocalDrafts.Tractability.ProductElimination

open Holant.Tractable Holant.Complexity
open Holant.Complexity.GraphPreprocessing.OriginalCoefficient
open scoped BigOperators

noncomputable section

variable {s b : ℕ} {arity : ℕ → ℕ}

structure FamilyData (s b : ℕ) (arity : ℕ → ℕ) where
  signatures : (i : Fin s) → Signature AlgebraicComplex (arity i.val)
  kernels : Fin b → Kernel AlgebraicComplex
  vertex : ∀ i, Presentation (signatures i)
  edge : ∀ i, Presentation (kernelSignature (kernels i))

variable (D : FamilyData s b arity)

def FamilyData.network (x : GraphListCompiler.Input s b arity) : Network AlgebraicComplex 0 :=
  x.val.realize x.property D.signatures D.kernels

def FamilyData.presentation (x : GraphListCompiler.Input s b arity) :
    NetworkPresentation (D.network x) where
  vertex v := D.vertex (x.val.signatureLabel x.property v)
  edge e := D.edge (x.val.edgeLabel x.property e)

def FamilyData.factors (x : GraphListCompiler.Input s b arity) :=
  networkFactors (D.network x) (D.presentation x)

def FamilyData.evaluate (x : GraphListCompiler.Input s b arity) : AlgebraicComplex :=
  ProductElimination.evaluate (D.factors x)

theorem FamilyData.evaluate_exact (x : GraphListCompiler.Input s b arity) :
    D.evaluate x = (D.network x).denote Fin.elim0 := evaluate_network _ _

/-- An explicit constant, fixed by the family, bounds every local template. -/
def FamilyData.templateBudget : ℕ :=
  (∑ i, (D.vertex i).factors.length) + ∑ i, (D.edge i).factors.length

theorem FamilyData.vertex_length_le (i : Fin s) :
    (D.vertex i).factors.length ≤ D.templateBudget := by
  have h := Finset.single_le_sum (f := fun j => (D.vertex j).factors.length)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  unfold FamilyData.templateBudget
  omega

theorem FamilyData.edge_length_le (i : Fin b) :
    (D.edge i).factors.length ≤ D.templateBudget := by
  have h := Finset.single_le_sum (f := fun j => (D.edge j).factors.length)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  unfold FamilyData.templateBudget
  omega

theorem FamilyData.factors_length_le (x : GraphListCompiler.Input s b arity) :
    (D.factors x).length ≤
      D.templateBudget * (x.val.vertices.length + x.val.edges.length) := by
  change (networkFactors (D.network x) (D.presentation x)).length ≤ _
  rw [networkFactors_length]
  have hv : (∑ v : Fin x.val.vertices.length,
      (D.vertex (x.val.signatureLabel x.property v)).factors.length) ≤
      x.val.vertices.length * D.templateBudget := by
    calc
      _ ≤ ∑ _ : Fin x.val.vertices.length, D.templateBudget :=
        Finset.sum_le_sum (fun v _ => D.vertex_length_le _)
      _ = _ := by simp
  have he : (∑ e : Fin x.val.edges.length,
      (D.edge (x.val.edgeLabel x.property e)).factors.length) ≤
      x.val.edges.length * D.templateBudget := by
    calc
      _ ≤ ∑ _ : Fin x.val.edges.length, D.templateBudget :=
        Finset.sum_le_sum (fun e _ => D.edge_length_le _)
      _ = _ := by simp
  change _ + _ ≤ _
  change (∑ v : Fin x.val.vertices.length, (D.vertex (x.val.signatureLabel x.property v)).factors.length) +
    (∑ e : Fin x.val.edges.length, (D.edge (x.val.edgeLabel x.property e)).factors.length) ≤ _
  simpa only [Nat.mul_add, Nat.add_mul, Nat.mul_comm] using Nat.add_le_add hv he

/-- Quadratic arithmetic bound in the number of original vertices and edges.
The factor-list expansion is linear with a fixed-family coefficient. -/
theorem FamilyData.operations_le (x : GraphListCompiler.Input s b arity) :
    (run (D.factors x)).2 ≤
      (4 * (x.val.vertices.length + x.val.edges.length) + 1) *
        (D.templateBudget * (x.val.vertices.length + x.val.edges.length)) +
        4 * (x.val.vertices.length + x.val.edges.length) := by
  have hr := run_operations_le (D.factors x)
  have hm := D.factors_length_le x
  have hn : (variableCount (D.network x)) = x.val.edges.length * 2 := by
    simp [variableCount, FamilyData.network, RawClosedNetwork.realize,
      RawClosedNetwork.shape, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  change (run (D.factors x)).2 ≤
    (2 * (variableCount (D.network x)) + 1) * (D.factors x).length +
      2 * (variableCount (D.network x)) at hr
  simp only [hn] at hr
  apply hr.trans
  have hsize : 2 * (x.val.edges.length * 2) ≤
      4 * (x.val.vertices.length + x.val.edges.length) := by omega
  exact Nat.add_le_add (Nat.mul_le_mul (Nat.add_le_add_right hsize 1) hm) hsize

/-- Input bit length also bounds the combinatorial parameter. This is still an
arithmetic bound, and makes no claim about intermediate rational bit lengths. -/
theorem FamilyData.operations_le_input_length (x : GraphListCompiler.Input s b arity) :
    let size := (RawClosedNetwork.encoding.encode x.val).length
    (run (D.factors x)).2 ≤
      (4 * size + 1) * (D.templateBudget * size) + 4 * size := by
  dsimp only
  have hsize := x.val.counts_le_encoded_length
  exact (D.operations_le x).trans
    (Nat.add_le_add
      (Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left D.templateBudget hsize))
      (by omega))

/-- Fixed data for a common product basis, including transformed edge tensors.
The fields are local Product formula data, never a global evaluation theorem. -/
structure CommonProductData (s b : ℕ) (arity : ℕ → ℕ) where
  signatures : (i : Fin s) → Signature AlgebraicComplex (arity i.val)
  kernels : Fin b → Kernel AlgebraicComplex
  basis : InvertibleKernel
  vertex : ∀ i, Presentation (basis.symm.action (signatures i))
  edge : ∀ i, Presentation (kernelSignature (Kernel.pullback (kernels i) basis.matrix))

variable (C : CommonProductData s b arity)

def CommonProductData.transformed : FamilyData s b arity where
  signatures i := C.basis.symm.action (C.signatures i)
  kernels i := Kernel.pullback (C.kernels i) C.basis.matrix
  vertex := C.vertex
  edge := C.edge

def CommonProductData.original (x : GraphListCompiler.Input s b arity) : Network AlgebraicComplex 0 :=
  x.val.realize x.property C.signatures C.kernels

theorem CommonProductData.transformed_network (x : GraphListCompiler.Input s b arity) :
    C.transformed.network x = (C.original x).holographicTransform C.basis.matrix C.basis.inverse := rfl

/-- Actual shared-basis product evaluation of the untransformed Holant problem. -/
theorem CommonProductData.evaluate_original (x : GraphListCompiler.Input s b arity) :
    C.transformed.evaluate x = (C.original x).denote Fin.elim0 := by
  rw [FamilyData.evaluate_exact, C.transformed_network]
  exact congrFun ((C.original x).denote_holographicTransform
    C.basis.matrix C.basis.inverse C.basis.matrix_inverse) Fin.elim0

/-- Source common-K-basis data produces all fixed local formulas, including X.
This is offline witness extraction; it is not effective recognition. -/
def commonKData (Gamma : SignatureFamily AlgebraicComplex)
    (sig : (i : Fin s) → Signature AlgebraicComplex (arity i.val))
    (hsig : ∀ i, (⟨arity i.val, sig i⟩ : AnySignature AlgebraicComplex) ∈ Gamma)
    (B : InvertibleKernel) (hB : IsCommonKBasis productClass Gamma B) :
    CommonProductData s 1 arity where
  signatures := sig
  kernels _ := Signature.disequality
  basis := B
  vertex i := ofProduct (hB.2 _ (hsig i))
  edge _ := ofProduct hB.1

/-- The ordinary-edge product branch of the literal TractX disjunction.
The common basis supplies local Product membership; elimination correctness
is proved above and is not a parameter of this construction. -/
def commonEqualityData (Gamma : SignatureFamily AlgebraicComplex)
    (sig : (i : Fin s) → Signature AlgebraicComplex (arity i.val))
    (hsig : ∀ i, (⟨arity i.val, sig i⟩ : AnySignature AlgebraicComplex) ∈ Gamma)
    (B : InvertibleKernel) (hB : IsCommonBasis productClass Gamma B) :
    CommonProductData s 1 arity where
  signatures := sig
  kernels _ := Signature.equality
  basis := B
  vertex i := ofProduct (hB.2 _ (hsig i))
  edge _ := ofProduct hB.1

/-- An actual evaluator for every raw graph over a common-product family.
This is deliberately an arithmetic algorithm existence theorem, not `InFP`.
Its templates and basis are fixed outside the universal instance quantifier. -/
theorem commonTransformable_evaluator
    (Gamma : SignatureFamily AlgebraicComplex)
    (sig : (i : Fin s) → Signature AlgebraicComplex (arity i.val))
    (hsig : ∀ i, (⟨arity i.val, sig i⟩ : AnySignature AlgebraicComplex) ∈ Gamma)
    (h : CommonTransformable productClass Gamma) :
    ∃ C : CommonProductData s 1 arity,
      C.signatures = sig ∧ C.kernels = (fun _ => Signature.equality) ∧
      ∀ x : GraphListCompiler.Input s 1 arity,
        C.transformed.evaluate x =
          (x.val.realize x.property sig (fun _ => Signature.equality)).denote Fin.elim0 := by
  obtain ⟨_, B, hB⟩ := h
  let C := commonEqualityData Gamma sig hsig B hB
  refine ⟨C, rfl, rfl, ?_⟩
  intro x
  exact C.evaluate_original x

end
end Holant.LocalDrafts.Tractability.ProductElimination
