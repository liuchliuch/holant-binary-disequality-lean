import Holant.ReedMuller.TwoChart.PhaseGluing
import Holant.ReedMuller.AffineRadon.NormalForm

/-! The literal complex affine class, retaining arbitrary complex exterior
scalars and the source's finite binary equations and even quadratic phases. -/
namespace Holant.Platonic.StabilizerLine
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.AffinePatching Holant.ReedMuller.AffineRadon
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

def ComplexAffine (f : Signature ℂ n) : Prop :=
  ∃ (c : ℂ) (g : Signature AlgebraicComplex n), Affine g ∧ ∀ x,f x=c*(g x:ℂ)

theorem complexAffine_of_affine {f : Signature AlgebraicComplex n} (hf : Affine f) :
    ComplexAffine (fun x => (f x:ℂ)) := ⟨1,f,hf,by simp⟩

theorem ComplexAffine.scale {f : Signature ℂ n} (hf : ComplexAffine f) (c : ℂ) :
    ComplexAffine (fun x => c*f x) := by
  obtain ⟨a,g,hg,he⟩ := hf
  exact ⟨c*a,g,hg,by intro x;dsimp;rw [he];ring⟩

structure NormalForm (f : Signature ℂ n) where
  scalar : ℂ
  scalar_ne_zero : scalar≠0
  shift : BinaryVector n
  direction : BinaryCode n
  phase : QuadraticPhase n
  exact_value : ∀ x : BinaryVector n,f (wordVector x)=
    if x-shift∈direction then scalar*(fourthRootPhase (phase.eval (wordVector x)):ℂ) else 0

theorem ComplexAffine.normalForm {f : Signature ℂ n} (hf : ComplexAffine f) (hn : f≠0) :
    Nonempty (NormalForm f) := by
  obtain ⟨c,g,hg,he⟩ := hf
  have hc : c≠0 := by intro h;apply hn;funext x;simp [he,h]
  have hgn : g≠0 := by intro h;apply hn;funext x;simp [he,h]
  obtain ⟨A⟩ := exists_actual_normal_form g hg hgn
  refine ⟨⟨c*(A.scalar:ℂ),mul_ne_zero hc (by exact_mod_cast A.scalar_ne_zero),
    A.shift,A.direction,A.phase,?_⟩⟩
  intro x
  rw [he,A.exact_value]
  split_ifs <;> simp [mul_assoc]

theorem NormalForm.support {f : Signature ℂ n} (A : NormalForm f) (x : BinaryVector n) :
    f (wordVector x)≠0 ↔ x-A.shift∈A.direction := by
  rw [A.exact_value]
  split_ifs with h
  · simp [h,mul_ne_zero A.scalar_ne_zero (show (fourthRootPhase _:ℂ)≠0 by
      exact_mod_cast fourthRootPhase_ne_zero _)]
  · simp [h]

theorem binary_self (x : BinaryVector n) : x+x=0 := by
  ext i
  exact CharTwo.add_self_eq_zero _

theorem NormalForm.ternary {f : Signature ℂ n} (A : NormalForm f)
    (x y z : BinaryVector n) (hx : f (wordVector x)≠0)
    (hy : f (wordVector y)≠0) (hz : f (wordVector z)≠0) :
    f (wordVector (x+y+z))≠0 := by
  apply (A.support _).mpr
  have h := A.direction.add_mem (A.direction.add_mem ((A.support _).mp hx)
    ((A.support _).mp hy)) ((A.support _).mp hz)
  convert h using 1
  ext i
  simp only [Pi.add_apply,Pi.sub_apply]
  have hh := CharTwo.add_self_eq_zero (A.shift i)
  linear_combination hh

theorem NormalForm.phase_cube {f : Signature ℂ n} (A : NormalForm f)
    (z u v w : BinaryVector n)
    (hz : z-A.shift∈A.direction) (hu : u∈A.direction)
    (hv : v∈A.direction) (hw : w∈A.direction) :
    f (wordVector (z+u+v+w))*f (wordVector (z+u))*f (wordVector (z+v))*f (wordVector (z+w))=
      f (wordVector (z+u+v))*f (wordVector (z+u+w))*f (wordVector (z+v+w))*f (wordVector z) := by
  have hmem (a : BinaryVector n) (ha : a∈A.direction) : z+a-A.shift∈A.direction := by
    convert A.direction.add_mem hz ha using 1 <;> abel
  have h := quadratic_phase_cross A.phase (wordVector z) (wordVector u) (wordVector v) (wordVector w)
  simp only [←word_add] at h
  have h' := congrArg (fun a : AlgebraicComplex => (a:ℂ)) h
  push_cast at h'
  have h2 (a b : BinaryVector n) (ha : a∈A.direction) (hb : b∈A.direction) :
      z+a+b-A.shift∈A.direction := by
    convert hmem (a+b) (A.direction.add_mem ha hb) using 1 <;> abel
  have h3 : z+u+v+w-A.shift∈A.direction := by
    convert hmem (u+v+w) (A.direction.add_mem (A.direction.add_mem hu hv) hw) using 1 <;> abel
  simp only [A.exact_value,if_pos hz,if_pos (hmem u hu),if_pos (hmem v hv),
    if_pos (hmem w hw),if_pos (h2 u v hu hv),if_pos (h2 u w hu hw),
    if_pos (h2 v w hv hw),if_pos h3]
  linear_combination A.scalar^4*h'

end
end Holant.Platonic.StabilizerLine
