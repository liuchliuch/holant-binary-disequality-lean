import Holant.Proofs.Dichotomy.Closure.Independent.GlobalCloseCompletionIndependentPinsTernaryAction
import Holant.Tractable.SymmetricBinaryPullback.Basic

/-! A prime ternary has two independent nonzero slices. An algebraic root
of their determinant pencil therefore gives a nonzero singular slice after
one genuine invertible semantic change of its first port. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIndependentPinsTernarySlices
open Holant Holant.Tractable Holant.LocalDrafts.FinitePGL2.Stabilization
open scoped BigOperators
namespace T
export GlobalCloseCompletionIndependentPinsTernaryAction (action ports prime_action)
end T
namespace Alg
export Holant.Tractable.SymmetricBinaryPullback (determinant invertibleOfDeterminant)
end Alg
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option maxRecDepth 16384
set_option Elab.async false

def slice (f : Signature AlgebraicComplex 3) (v : Bool) : Kernel AlgebraicComplex:=fun i j=>f ![v,i,j]
def pack (S U : Kernel AlgebraicComplex) : Signature AlgebraicComplex 3 := fun x=>if x 0 then U (x 1) (x 2) else S (x 1) (x 2)

theorem word (x : Fin 3→Bool) : ![x 0,x 1,x 2]=x := by funext i;fin_cases i <;> rfl

theorem pack_slices (f : Signature AlgebraicComplex 3) : pack (slice f false) (slice f true)=f := by
  funext x
  have hx:=congrArg f (word x)
  cases e : x 0 <;> simpa only [pack,slice,e,Bool.false_eq_true,ite_false,ite_true] using hx

private def splitPorts : (Fin 1⊕Fin 2)≃Fin 3:=finSumFinEquiv

theorem not_first_product (f : Signature AlgebraicComplex 3)
    (prime : Prime (⟨3,f⟩ : AnySignature AlgebraicComplex))
    (u : Signature AlgebraicComplex 1) (g : Signature AlgebraicComplex 2) :
    f≠(fun x=>u (fun _=>x 0)*g ![x 1,x 2]) := by
  intro form
  apply prime.2
  refine ⟨⟨1,u⟩,⟨2,g⟩,⟨{
    left_pos:=by change 0<1;omega
    right_pos:=by change 0<2;omega
    ports:=splitPorts
    scale:=1
    equation:=?_ }⟩⟩
  rw [form]
  funext x
  have left : (fun i : Fin 1=>x (splitPorts (.inl i)))=(fun _=>x 0) := by funext i;fin_cases i;rfl
  have right : (fun i : Fin 2=>x (splitPorts (.inr i)))=![x 1,x 2] := by funext i;fin_cases i <;> rfl
  change _=(1:AlgebraicComplex)*(u _*g _)
  rw [left,right,one_mul]

theorem slice_nonzero (f : Signature AlgebraicComplex 3)
    (prime : Prime (⟨3,f⟩ : AnySignature AlgebraicComplex)) (v : Bool) : slice f v≠0 := by
  intro zero
  apply not_first_product f prime (fun x=>if x 0=v then 0 else 1)
    (fun x=>slice f (!v) (x 0) (x 1))
  rw [←pack_slices f]
  funext x
  cases v <;> cases e : x 0 <;> simp [pack,slice,e] at zero ⊢
  all_goals first
    | exact congrFun₂ zero (x 1) (x 2)
    | rfl

theorem not_parallel (f : Signature AlgebraicComplex 3)
    (prime : Prime (⟨3,f⟩ : AnySignature AlgebraicComplex)) (v : Bool) (c : AlgebraicComplex) :
    slice f v≠(fun i j=>c*slice f (!v) i j) := by
  intro same
  apply not_first_product f prime (fun x=>if x 0=v then c else 1)
    (fun x=>slice f (!v) (x 0) (x 1))
  rw [←pack_slices f]
  funext x
  cases v <;> cases e : x 0 <;> simp only [pack,slice,e,Bool.not_false,Bool.not_true,
    Bool.false_eq_true,Bool.true_eq_false,ite_false,ite_true,one_mul] at same ⊢
  all_goals first | exact congrFun₂ same (x 1) (x 2) | rfl

theorem pencil_nonzero (f : Signature AlgebraicComplex 3)
    (prime : Prime (⟨3,f⟩ : AnySignature AlgebraicComplex)) (c : AlgebraicComplex) :
    (fun i j=>slice f false i j+c*slice f true i j)≠0 := by
  intro zero
  apply not_parallel f prime false (-c)
  funext i j
  have hz:=congrFun₂ zero i j
  change slice f false i j+c*slice f true i j=0 at hz
  change slice f false i j= -c*slice f true i j
  linear_combination hz

theorem first_action (A : InvertibleKernel) (f : Signature AlgebraicComplex 3) (x : Fin 3→Bool) :
    T.action A InvertibleKernel.identity InvertibleKernel.identity f x=
      A.matrix (x 0) false*slice f false (x 1) (x 2)+A.matrix (x 0) true*slice f true (x 1) (x 2) := by
  simp only [T.action,Signature.coordinateAction,GlobalCloseCompletionTernaryGHZAction.sum_words]
  cases e1 : x 1 <;> cases e2 : x 2 <;>
    simp [T.ports,InvertibleKernel.identity,Fin.prod_univ_three,Signature.equality,slice,e1,e2]
  all_goals ring

theorem identity_action (f : Signature AlgebraicComplex 3) :
    T.action InvertibleKernel.identity InvertibleKernel.identity InvertibleKernel.identity f=f := by
  change Signature.coordinateAction (fun _=>Signature.equality) f=f
  exact Signature.coordinateAction_equality f

def mixed (S U : Kernel AlgebraicComplex) : AlgebraicComplex :=
  S false false*U true true+U false false*S true true-S false true*U true false-U false true*S true false

theorem determinant_pencil (S U : Kernel AlgebraicComplex) (c : AlgebraicComplex) :
    Alg.determinant (fun i j=>S i j+c*U i j)=
      Alg.determinant U*c^2+mixed S U*c+Alg.determinant S := by
  simp only [Alg.determinant,mixed]
  ring

theorem quadratic_root (a b c : AlgebraicComplex) (ha : a≠0) :
    ∃t : AlgebraicComplex,a*t^2+b*t+c=0 := by
  letI : IsAlgClosed AlgebraicComplex := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨d,hd⟩:=IsAlgClosed.exists_pow_nat_eq (b^2-4*a*c) (by decide : 0<2)
  refine ⟨(-b+d)/(2*a),?_⟩
  field_simp [ha]
  linear_combination hd

def shear (c : AlgebraicComplex) : InvertibleKernel :=
  Alg.invertibleOfDeterminant
    (fun i j=>if i then (if j then c else 1) else (if j then 1 else 0))
    (by norm_num [Alg.determinant])

theorem shear_slice (f : Signature AlgebraicComplex 3) (c : AlgebraicComplex) :
    slice (T.action (shear c) InvertibleKernel.identity InvertibleKernel.identity f) true=
      fun i j=>slice f false i j+c*slice f true i j := by
  funext i j
  rw [slice,first_action]
  simp [shear,Alg.invertibleOfDeterminant]

theorem singular_slice (f : Signature AlgebraicComplex 3)
    (prime : Prime (⟨3,f⟩ : AnySignature AlgebraicComplex)) :
    ∃A : InvertibleKernel,
      let g:=T.action A InvertibleKernel.identity InvertibleKernel.identity f
      slice g true≠0 ∧ Alg.determinant (slice g true)=0 := by
  by_cases singular : Alg.determinant (slice f true)=0
  · refine ⟨InvertibleKernel.identity,?_⟩
    simpa only [identity_action] using And.intro (slice_nonzero f prime true) singular
  · obtain ⟨c,hc⟩:=quadratic_root (Alg.determinant (slice f true))
      (mixed (slice f false) (slice f true)) (Alg.determinant (slice f false)) singular
    refine ⟨shear c,?_⟩
    dsimp only
    rw [shear_slice]
    exact ⟨pencil_nonzero f prime c,by rw [determinant_pencil];exact hc⟩

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIndependentPinsTernarySlices
end
