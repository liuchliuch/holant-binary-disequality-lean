import Holant.ReedMuller.FlatNetwork.Fibres
import Holant.Kernel
import Holant.ReedMuller.FlatNetwork.Parity
import Holant.ReedMuller.LowArity.FlatSignature

/-! Exact binary-coordinate transport and the signature-level local closure.
The Boolean network tensors and the F2 code tensors are explicitly identified. -/
namespace Holant.ReedMuller.FlatNetwork
open Holant Holant.ReedMuller.LowArity
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

variable {m n : ℕ}

def boolEquiv : Bool ≃ ZMod 2 where
  toFun := fun b => if b then 1 else 0
  invFun := fun a => decide (a=1)
  left_inv := by intro b;cases b <;> decide
  right_inv := by intro a;fin_cases a <;> decide

def vectorWord (x : Fin n → Bool) : BinaryVector n := fun i => boolEquiv (x i)
def wordVector (x : BinaryVector n) : Fin n → Bool := fun i => boolEquiv.symm (x i)

@[simp] theorem vector_word (x : BinaryVector n) : vectorWord (wordVector x)=x := by
  funext i
  exact boolEquiv.apply_symm_apply _
@[simp] theorem word_vector (x : Fin n → Bool) : wordVector (vectorWord x)=x := by
  funext i
  exact boolEquiv.symm_apply_apply _

def Flat (f : Signature ℂ n) : Prop :=
  ∃ (c : ℂˣ) (a : BinaryVector n) (D : BinaryCode n),SelfDual D ∧ f=flatSignature c a D

def FlatOrZero (f : Signature ℂ n) : Prop := f=0 ∨ Flat f

theorem flatSignature_vector (c : ℂˣ) (a : BinaryVector n) (D : BinaryCode n) (x : Fin n → Bool) :
    flatSignature c a D x=flatValue c a D (vectorWord x) := rfl

def parityKernel (eta : ZMod 2) : Kernel ℂ := fun a b => if boolEquiv a+boolEquiv b=eta then 1 else 0

@[simp] theorem parityKernel_zero : parityKernel 0=Signature.equality := by
  funext a b
  have htwo : (2 : ZMod 2)=0 := by decide
  have hadd : (1 : ZMod 2)+1=0 := by decide
  cases a <;> cases b <;> norm_num [parityKernel,boolEquiv,Signature.equality,Signature.disequality,htwo,hadd]
@[simp] theorem parityKernel_one : parityKernel 1=Signature.disequality := by
  funext a b
  have htwo : (2 : ZMod 2)=0 := by decide
  have hadd : (1 : ZMod 2)+1=0 := by decide
  cases a <;> cases b <;> norm_num [parityKernel,boolEquiv,Signature.equality,Signature.disequality,htwo,hadd]

theorem vector_cons (a b : Bool) (x : Fin n → Bool) :
    vectorWord (Fin.cons a (Fin.cons b x))=Fin.cons (boolEquiv a) (Fin.cons (boolEquiv b) (vectorWord x)) := by
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  refine Fin.cases rfl (fun k => ?_) j
  rfl

theorem closeValue_eq_contract (eta : ZMod 2) (f : BinaryVector (n+2) → ℂ)
    (x : Fin n → Bool) :
    Signature.contract (parityKernel eta) (fun y => f (vectorWord y)) x=closeValue eta f (vectorWord x) := by
  have H : ∑ b : Bool,f (lift eta (boolEquiv b) (vectorWord x))=
      ∑ b : ZMod 2,f (lift eta b (vectorWord x)) := boolEquiv.sum_comp (fun b : ZMod 2 => f (lift eta b (vectorWord x)))
  rw [closeValue,←H]
  unfold Signature.contract
  simp only [Fintype.sum_bool,vector_cons]
  have hadd : (1 : ZMod 2)+1=0 := by decide
  have htwo : (2 : ZMod 2)=0 := by decide
  fin_cases eta <;> simp [parityKernel,boolEquiv,lift,hadd,htwo]

theorem flat_contract (f : Signature ℂ (n+2)) (hf : Flat f) (eta : ZMod 2) :
    FlatOrZero (Signature.contract (parityKernel eta) f) := by
  obtain ⟨c,a,D,hD,rfl⟩ := hf
  have hformula : Signature.contract (parityKernel eta) (flatSignature c a D)=
      fun x => closeValue eta (flatValue c a D) (vectorWord x) := by
    funext x
    exact closeValue_eq_contract eta (flatValue c a D) x
  rw [hformula]
  rcases close_flat_selfDual D hD a c c.ne_zero eta with hz | ⟨a',he,hn,hproj⟩
  · left
    rw [hz]
    rfl
  · right
    refine ⟨Units.mk0 ((c:ℂ)*fiberMultiplier D) hn,a',equalProjection D,hproj,?_⟩
    funext x
    rw [he]
    rfl

theorem flatOrZero_contract (f : Signature ℂ (n+2)) (hf : FlatOrZero f) (eta : ZMod 2) :
    FlatOrZero (Signature.contract (parityKernel eta) f) := by
  rcases hf with rfl | h
  · left
    funext x
    simp [Signature.contract]
  · exact flat_contract f h eta

theorem flat_arity_even (f : Signature ℂ n) (hf : Flat f) : Even n := by
  obtain ⟨c,a,D,hD,rfl⟩ := hf
  exact selfDual_arity_even D hD

end
end Holant.ReedMuller.FlatNetwork
