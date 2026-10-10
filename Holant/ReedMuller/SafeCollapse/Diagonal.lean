import Holant.ReedMuller.CoefficientAtlas.Source
import Holant.Observability.Consequences
import Holant.OpenNetworkComposition.Closure
import Mathlib.Tactic.FieldSimp

/-! Actual first-port transfer dressing and its Walsh diagonal form. -/
namespace Holant.ReedMuller.SafeCollapse
open Holant Holant.ReedMuller.CoefficientAtlas
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

abbrev Mat := Kernel ℂ

def mix (a b : ℂ) : Mat := fun x y => if x=y then a else b
def diag (a b : ℂ) : Mat := fun x y => if x=y then if x then b else a else 0
def det (A : Mat) : ℂ := A false false*A true true-A false true*A true false

def onePort {n : ℕ} (q : Signature ℂ n) (T : Mat) (p : Fin n) : Signature ℂ n :=
  Signature.coordinateAction (fun j => if j=p then T else Signature.equality) q

theorem proper_mix (T : Mat) (hT : T∈Observability.ixSpan) : T=mix (T false false) (T false true) := by
  obtain ⟨hd,ho⟩ := (Observability.mem_ixSpan_iff T).mp hT
  funext x y
  cases x <;> cases y <;> simp [mix,hd,ho]

theorem walsh_mix (a b : ℂ) :
    Kernel.mul (Kernel.mul walshInverse (mix a b)) walshKernel=diag (a+b) (a-b) := by
  funext x y
  cases x <;> cases y <;>
    simp [Kernel.mul_apply,walshInverse,walshKernel,mix,diag] <;> ring

theorem mix_eigenvalues_nonzero (a b : ℂ) (h : det (mix a b)≠0) : a+b≠0 ∧ a-b≠0 := by
  have he : det (mix a b)=(a+b)*(a-b) := by simp [det,mix];ring
  rw [he] at h
  exact mul_ne_zero_iff.mp h

theorem walsh_onePort {n : ℕ} (q : Signature ℂ n) (T : Mat) (p : Fin n) :
    walsh (onePort q T p)=onePort (walsh q)
      (Kernel.mul (Kernel.mul walshInverse T) walshKernel) p := by
  conv_lhs => rw [←physical_of_walsh q]
  simp only [walsh,onePort,Signature.coordinateAction_comp]
  congr 1
  funext j
  by_cases hj : j=p <;> simp [hj,Kernel.mul_assoc,walsh_mul_inverse]

theorem onePort_diagonal {n : ℕ} (q : Signature ℂ n) (a b : ℂ) (p : Fin n) (x : Fin n → Bool) :
    onePort q (diag a b) p x=(if x p then b else a)*q x := by
  have hm (j : Fin n) (u v : Bool) :
      (if j=p then diag a b else Signature.equality) u v=
        (if j=p then if u then b else a else 1)*Signature.equality u v := by
    by_cases hj : j=p <;> cases u <;> cases v <;> simp [hj,diag,Signature.equality]
  simp only [onePort,Signature.coordinateAction,hm,Finset.prod_mul_distrib,Signature.prod_equality]
  simp

theorem walsh_onePort_mix {n : ℕ} (q : Signature ℂ n) (a b : ℂ) (p : Fin n) (x : Fin n → Bool) :
    walsh (onePort q (mix a b) p) x=(if x p then a-b else a+b)*walsh q x := by
  rw [walsh_onePort,walsh_mix,onePort_diagonal]

theorem supportRM_onePort_mix (q : Signature ℂ 8) (hs : SupportRM (walsh q))
    (a b : ℂ) (hdet : det (mix a b)≠0) (p : Fin 8) :
    SupportRM (walsh (onePort q (mix a b) p)) := by
  have hn := mix_eigenvalues_nonzero a b hdet
  intro x
  rw [walsh_onePort_mix]
  have hfactor : (if x p then a-b else a+b)≠0 := by cases x p <;> simp [hn.1,hn.2]
  rw [mul_ne_zero_iff]
  constructor
  · intro h
    exact (hs x).mp h.2
  · intro h
    exact ⟨hfactor,(hs x).mpr h⟩

end
end Holant.ReedMuller.SafeCollapse
