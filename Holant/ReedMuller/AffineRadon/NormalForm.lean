import Holant.ReedMuller.AffinePatching.BooleanLinear

/-! A nonzero member of the manuscript affine class has a genuine affine
support coset: its direction is constructed as the kernel of its actual
finite support system. This is not an additional recognition hypothesis. -/
namespace Holant.ReedMuller.AffineRadon
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

def systemMap (S : AffineSystem n) : BinaryVector n →ₗ[ZMod 2] BinaryVector S.rows where
  toFun x := fun r => ∑ i,S.matrix r i*x i
  map_add' := by intro x y;funext r;simp [mul_add,Finset.sum_add_distrib]
  map_smul' := by
    intro c x
    funext r
    simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

def systemDirection (S : AffineSystem n) : BinaryCode n := LinearMap.ker (systemMap S)

 theorem system_holds_vector (S : AffineSystem n) (x : BinaryVector n) :
    S.Holds (wordVector x) ↔ systemMap S x=S.rhs := by
  have hb (i : Fin n) : bitValue (ZMod 2) (wordVector x i)=x i := by
    exact boolEquiv.apply_symm_apply _
  simp only [AffineSystem.Holds,hb,systemMap,LinearMap.coe_mk,AddHom.coe_mk]
  exact funext_iff.symm

 theorem system_holds_coset (S : AffineSystem n) (a : BinaryVector n)
    (ha : S.Holds (wordVector a)) (x : BinaryVector n) :
    S.Holds (wordVector x) ↔ x-a∈systemDirection S := by
  have ha' := (system_holds_vector S a).mp ha
  rw [system_holds_vector]
  change systemMap S x=S.rhs ↔ systemMap S (x-a)=0
  rw [map_sub,ha',sub_eq_zero]

structure ActualNormalForm (f : Signature AlgebraicComplex n) where
  scalar : AlgebraicComplex
  scalar_ne_zero : scalar≠0
  shift : BinaryVector n
  direction : BinaryCode n
  phase : QuadraticPhase n
  exact_value : ∀ x : BinaryVector n,f (wordVector x)=
    if x-shift∈direction then scalar*fourthRootPhase (phase.eval (wordVector x)) else 0

 theorem exists_actual_normal_form (f : Signature AlgebraicComplex n) (hf : Affine f) (hn : f≠0) :
    Nonempty (ActualNormalForm f) := by
  rcases hf with hz | ⟨c,hc,S,Q,he⟩
  · exact False.elim (hn hz)
  have hex : ∃ a : Word n,f a≠0 := by
    by_contra h
    push_neg at h
    exact hn (funext h)
  obtain ⟨a,ha⟩ := hex
  have hS : S.Holds a := by
    by_contra h
    exact ha (by rw [he];simp [affineFormula,h])
  refine ⟨⟨c,hc,vectorWord a,systemDirection S,Q,?_⟩⟩
  intro x
  rw [he]
  unfold affineFormula
  simp only [system_holds_coset S (vectorWord a) (by simpa using hS) x]

 theorem ActualNormalForm.support (f : Signature AlgebraicComplex n) (A : ActualNormalForm f)
    (x : BinaryVector n) : f (wordVector x)≠0 ↔ x-A.shift∈A.direction := by
  rw [A.exact_value]
  split_ifs with h
  · simp [h,mul_ne_zero A.scalar_ne_zero (fourthRootPhase_ne_zero _)]
  · simp [h]

end
end Holant.ReedMuller.AffineRadon
