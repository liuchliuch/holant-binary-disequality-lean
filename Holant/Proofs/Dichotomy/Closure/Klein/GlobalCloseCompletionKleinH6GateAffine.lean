import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinH6GateAlgebra

/-! The actual H6 front-three operator and its transpose preserve affinity.
The reverse implication uses the proved inverse, with its nonzero factor four. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinH6GateAffine
open Holant Holant.Tractable
namespace A
export GlobalCloseCompletionKleinH6GateAlgebra (front tail append action sum_three inverse)
end A
namespace D
export GlobalCloseCompletionKleinH6GateData (Word3 join matrix_cast)
end D
namespace H
export GlobalCloseCompletionKleinH6RMBell (core core_algebraic)
end H
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384
set_option Elab.async false
variable {n : ℕ}

def corePorts (b : Bool) : Fin 6→Fin (n+6) :=
  if b then ![0,1,2,3,4,5] else ![3,4,5,0,1,2]
def inputPorts : Fin (n+3)→Fin (n+6) :=
  Fin.cases 0 (Fin.cases 1 (Fin.cases 2 (fun i=>i.succ.succ.succ.succ.succ.succ)))
def kernel (b : Bool) (f : Signature AlgebraicComplex (n+3)) : Signature AlgebraicComplex (n+6) :=
  fun x=>H.core (fun i=>x (corePorts b i))*f (fun i=>x (inputPorts i))

theorem value (b : Bool) (f : Signature AlgebraicComplex (n+3)) (u : D.Word3) (x : Fin (n+3)→Bool) :
    kernel b f (A.append u x)=
      (GlobalCloseCompletionKleinH6GateData.matrix b (A.front x) u:AlgebraicComplex)*f (A.append u (A.tail x)) := by
  rw [D.matrix_cast]
  cases b <;> simp only [kernel,corePorts,Bool.false_eq_true,ite_false,ite_true]
  all_goals congr 1
  all_goals
    apply congrArg f
    funext i
    refine Fin.cases ?_ (fun i=>?_) i
    · rfl
    · refine Fin.cases ?_ (fun i=>?_) i
      · rfl
      · refine Fin.cases ?_ (fun i=>?_) i <;> rfl

theorem kernel_affine (b : Bool) (f : Signature AlgebraicComplex (n+3)) (affine : Affine f) : Affine (kernel b f) := by
  have core : Affine (H.core (K:=AlgebraicComplex)) := by
    rw [H.core_algebraic]
    exact GlobalCloseCompletionKleinStandardCoreAffine.affine_core
  exact (core.precompose _ (coordinates_isAffineMap (corePorts b))).mul
    (affine.precompose _ (coordinates_isAffineMap inputPorts))

theorem action_affine (b : Bool) (f : Signature AlgebraicComplex (n+3)) (affine : Affine f) : Affine (A.action b f) := by
  have h := (kernel_affine b f affine).sum_first.sum_first.sum_first
  convert h using 1
  funext x
  have point (a d e : Bool) :
      kernel b f (Fin.cons a (Fin.cons d (Fin.cons e x)))=
        (GlobalCloseCompletionKleinH6GateData.matrix b (A.front x) ![a,d,e]:AlgebraicComplex)*
          f (A.append ![a,d,e] (A.tail x)) := value b f ![a,d,e] x
  simp only [A.action,A.sum_three,Fintype.sum_bool,point]
  ac_rfl

theorem action_affine_iff (b : Bool) (f : Signature AlgebraicComplex (n+3)) : Affine (A.action b f) ↔ Affine f := by
  constructor
  · intro affine
    have h := action_affine (!b) _ affine
    have h := h.scale (4:AlgebraicComplex)⁻¹
    rw [A.inverse] at h
    convert h using 1
    funext x
    change f x=(4:AlgebraicComplex)⁻¹*(4*f x)
    field_simp
  · exact action_affine b f

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinH6GateAffine
end
