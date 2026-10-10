import Holant.Proofs.Algorithms.KSourceTransport
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeCubicGadgets

/-! Exact symmetric GHZ coordinates. The Gram edge and the two orientations
of the retained pin are distinguished. These identities do not install a
matrix or an equality tensor as a physical resource. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSymmetricGHZCoordinates
open Holant Holant.Tractable
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
set_option Elab.async false
variable {K : Type} [Field K]

def eq3 : Signature K 3 := fun x=>
  (if x=(fun _=>false) then 1 else 0)+(if x=(fun _=>true) then 1 else 0)

theorem eq3_value (x : Fin 3→Bool) : eq3 (K:=K) x=if x 0=x 1 ∧ x 1=x 2 then 1 else 0 := by
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;>
    simp [eq3,funext_iff,Fin.forall_fin_succ,h0,h1,h2]

def gram (M : Kernel K) : Kernel K := Kernel.pullback Signature.equality M

theorem gram_value (M : Kernel K) (p q : Bool) :
    gram M p q=M false p*M false q+M true p*M true q := by
  simp [gram,Kernel.pullback,Kernel.mul,Kernel.transpose,Signature.equality]
  ring

theorem gram_symmetric (M : Kernel K) : Kernel.transpose (gram M)=gram M := by
  funext p q
  simp only [Kernel.transpose,gram_value]
  ring

def ghz (M : Kernel K) : Signature K 3 := Signature.coordinateAction (fun _=>M) eq3

theorem ghz_value (M : Kernel K) (x : Fin 3→Bool) :
    ghz M x=M (x 0) false*M (x 1) false*M (x 2) false+
      M (x 0) true*M (x 1) true*M (x 2) true := by
  simp [ghz,Signature.coordinateAction,eq3,mul_add,Finset.sum_add_distrib,Fin.prod_univ_succ,mul_assoc]

theorem inverse_ghz (M N : Kernel K) (inverse : Kernel.mul N M=Signature.equality) :
    Signature.coordinateAction (fun _=>N) (ghz M)=eq3 :=
  Signature.coordinateAction_cancel _ _ (fun _=>inverse) eq3

def pin (v : Bool) : Signature K 1 := fun x=>if x 0=v then 1 else 0

theorem pin_action (M : Kernel K) (v : Bool) :
    Signature.coordinateAction (fun _=>M) (pin v)=fun x=>M (x 0) v := by
  funext x
  unfold Signature.coordinateAction
  rw [←(Equiv.funUnique (Fin 1) Bool).symm.sum_comp]
  cases v <;> simp [pin]

/-- A left pin is a covector: it transforms by the transpose, and is not
the right-hand inverse-transformed pin. -/
theorem left_pin (M : Kernel K) :
    Signature.coordinateAction (fun _=>Kernel.transpose M) (pin false)=fun x=>M false (x 0) :=
  pin_action (Kernel.transpose M) false

theorem right_pin (N : Kernel K) :
    Signature.coordinateAction (fun _=>N) (pin false)=fun x=>N (x 0) false :=
  pin_action N false

theorem gram_det (M : Kernel K) :
    gram M false false*gram M true true-gram M false true*gram M true false=
      (M false false*M true true-M false true*M true false)^2 := by
  simp only [gram_value]
  ring

theorem isotropic_pin_nonzero (M : Kernel K)
    (det : M false false*M true true-M false true*M true false≠0)
    (first : gram M false false=0) (second : gram M true true=0) :
    M false false≠0 ∧ M false true≠0 := by
  constructor
  · intro h
    have hc : M true false=0 := by
      have sq : M true false^2=0 := by simpa [gram_value,h,pow_two] using first
      by_contra nonzero
      exact pow_ne_zero 2 nonzero sq
    exact det (by simp [h,hc])
  · intro h
    have hd : M true true=0 := by
      have sq : M true true^2=0 := by simpa [gram_value,h,pow_two] using second
      by_contra nonzero
      exact pow_ne_zero 2 nonzero sq
    exact det (by simp [h,hd])


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSymmetricGHZCoordinates
end
