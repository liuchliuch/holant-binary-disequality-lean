import Holant.Proofs.Dichotomy.Closure.Ternary.GlobalCloseCompletionTernaryGHZException

/-! Cyclic invariance of a Boolean ternary is full symmetry. The explicit
four coefficients retain every value, so consumers need no symmetry oracle. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionTernaryGHZSymmetry
open Holant
namespace T
export GlobalCloseCompletionTernaryGHZCore (cyclic triangle triangle_cyclic ghz)
end T
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
set_option Elab.async false
variable {K : Type} [Field K]

def symmetric (v : Fin 4→K) : Signature K 3 := fun x=>
  if x 0 then (if x 1 then (if x 2 then v 3 else v 2) else (if x 2 then v 2 else v 1))
  else if x 1 then (if x 2 then v 2 else v 1) else (if x 2 then v 1 else v 0)

def values (f : Signature K 3) : Fin 4→K :=
  ![f ![false,false,false],f ![true,false,false],f ![true,true,false],f ![true,true,true]]

theorem of_cyclic (f : Signature K 3) (cyclic : ∀x,f (T.cyclic x)=f x) : f=symmetric (values f) := by
  have h1:=cyclic ![false,false,true]
  have h2:=cyclic ![false,true,false]
  have h3:=cyclic ![false,true,true]
  have h4:=cyclic ![true,false,true]
  simp [T.cyclic] at h1 h2 h3 h4
  funext x
  have hx : x=![x 0,x 1,x 2] := by funext i;fin_cases i <;> rfl
  rw [hx]
  cases x 0 <;> cases x 1 <;> cases x 2 <;> simp [symmetric,values]
  · exact h1.symm.trans h2.symm
  · exact h2.symm
  · exact h3.symm
  · exact h4.symm.trans h3.symm

theorem triangle (f : Signature K 3) : T.triangle f=symmetric (values (T.triangle f)) :=
  of_cyclic _ (T.triangle_cyclic f)

variable (A B C : Matrix Bool Bool K) (ha : A.det≠0) (hb : B.det≠0) (hc : C.det≠0)
variable (ab : ∀t,(A.transpose*B) t t=0)
variable (bc : ∀t,(B.transpose*C) t t=0)
variable (ca : ∀t,(C.transpose*A) t t=0)
include ha hb hc ab bc ca in
theorem exception : T.ghz A B C=symmetric (values (T.ghz A B C)) := by
  apply of_cyclic
  intro x
  have h1:=GlobalCloseCompletionTernaryGHZException.swap01 A B C hb hc ab bc ca x
  -- Two adjacent swaps cyclically rotate the exact three coordinates.
  have direct:=GlobalCloseCompletionTernaryGHZException.swap12 A B C ha hb ab bc ca ![x 1,x 0,x 2]
  simpa [T.cyclic] using direct.trans h1


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionTernaryGHZSymmetry
end
