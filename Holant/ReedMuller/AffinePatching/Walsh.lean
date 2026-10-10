import Holant.ReedMuller.AffinePatching.BlockPorts

/-! The unnormalized Walsh transform preserves the manuscript's actual
finite-equation/even-quadratic affine class by literal variable elimination. -/
namespace Holant.ReedMuller.AffinePatching
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

def hadamard (a b : Bool) : AlgebraicComplex := if a && b then -1 else 1

def hadamardPhase : QuadraticPhase 2 where
  constant := 0
  linear := fun _ => 0
  mixed := fun j k => if j=0 ∧ k=1 then 2 else 0
  even_mixed := by intro j k _;split_ifs <;> simp

theorem hadamard_affine : Affine (fun x : Word 2 => hadamard (x 0) (x 1)) := by
  have h := affine_formula 1 (AffineSystem.unconstrained 2) hadamardPhase
  convert h using 1
  funext x
  cases ha : x 0 <;> cases hb : x 1 <;>
    norm_num [affineFormula,hadamard,QuadraticPhase.eval,hadamardPhase,
      Fin.sum_univ_succ,ha,hb,bitValue]

def walshKernel (x y : Word n) : AlgebraicComplex := ∏ i,hadamard (x i) (y i)
def walsh (f : Signature AlgebraicComplex n) : Signature AlgebraicComplex n :=
  fun x => ∑ y,walshKernel x y*f y

def walshJoint (f : Signature AlgebraicComplex n) : Signature AlgebraicComplex (n+n) :=
  fun z => (∏ i,hadamard (z (suffixPort n n i)) (z (prefixPort n n i)))*
    f (fun i => z (prefixPort n n i))

theorem walshJoint_affine (f : Signature AlgebraicComplex n) (hf : Affine f) :
    Affine (walshJoint f) := by
  have hk : Affine (fun z : Word (n+n) =>
      ∏ i,hadamard (z (suffixPort n n i)) (z (prefixPort n n i))) := by
    apply affine_finset_prod Finset.univ
    intro i _
    let idx : Fin 2 → Fin (n+n) := ![suffixPort n n i,prefixPort n n i]
    have h := hadamard_affine.precompose (fun z j => z (idx j)) (coordinates_isAffineMap idx)
    exact h
  exact hk.mul (hf.precompose _ (coordinates_isAffineMap (prefixPort n n)))

theorem walsh_eq_sumVariables (f : Signature AlgebraicComplex n) :
    walsh f=sumVariables n n (walshJoint f) := by
  funext x
  rw [sumVariables_eq]
  simp only [walsh,walshJoint,insertWord_prefix,insertWord_suffix,walshKernel]

 theorem walsh_affine (f : Signature AlgebraicComplex n) (hf : Affine f) : Affine (walsh f) := by
  rw [walsh_eq_sumVariables]
  exact sumVariables_affine n n _ (walshJoint_affine f hf)

end
end Holant.ReedMuller.AffinePatching
