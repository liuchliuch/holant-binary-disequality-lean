import Holant.Certificates.FourthRootOdd.ExceptionalData
import Holant.Tractable.AffinePhase.Roots

/-! The literal odd-coset chart and modulo-four phase test from the source.
The phase shift is an analytic table operation, not an assumed available gadget. -/
namespace Holant.Certificates.FourthRootOdd
open Holant Holant.Certificates.TwelveLoops Holant.Tractable

def oddChart (y : Fin 3 → Bool) : Fin 4 → Bool :=
  ![y 0,y 1,y 2,!(y 0 ^^ y 1 ^^ y 2)]

def phaseAt (s : State) (δ : Fin 4) (x : Fin 4 → Bool) : ZMod 4 :=
  match x 0,x 1,x 2,x 3 with
  | true,false,false,false => (alpha s 0).val
  | false,true,false,false => (alpha s 1).val
  | false,false,true,false => (alpha s 2).val
  | false,false,false,true => (alpha s 3).val
  | false,true,true,true => (beta s 0).val+δ.val
  | true,false,true,true => (beta s 1).val+δ.val
  | true,true,false,true => (beta s 2).val+δ.val
  | true,true,true,false => (beta s 3).val+δ.val
  | _,_,_,_ => 0

def chartPhase (s : State) (δ : Fin 4) : (Fin 3 → Bool) → ZMod 4 :=
  fun y => phaseAt s δ (oddChart y)

def origin3 : Fin 3 → Bool := ![false,false,false]
def unit3 (i : Fin 3) : Fin 3 → Bool := fun j => decide (j=i)
def pair3 (i j : Fin 3) : Fin 3 → Bool := fun k => decide (k=i ∨ k=j)

def phaseLinear (φ : (Fin 3 → Bool) → ZMod 4) (i : Fin 3) : ZMod 4 := φ (unit3 i)-φ origin3
def phaseMixed (φ : (Fin 3 → Bool) → ZMod 4) (i j : Fin 3) : ZMod 4 :=
  φ (pair3 i j)-φ (unit3 i)-φ (unit3 j)+φ origin3

def PhaseCriterion (φ : (Fin 3 → Bool) → ZMod 4) : Prop :=
  (∀ i j : Fin 3, i<j → phaseMixed φ i j=0 ∨ phaseMixed φ i j=2) ∧
  φ ![true,true,true]=φ origin3+phaseLinear φ 0+phaseLinear φ 1+phaseLinear φ 2+
    phaseMixed φ 0 1+phaseMixed φ 0 2+phaseMixed φ 1 2
instance (φ : (Fin 3 → Bool) → ZMod 4) : Decidable (PhaseCriterion φ) :=
  inferInstanceAs (Decidable (_ ∧ _))

def phaseTest (s : State) (δ : Fin 4) : Prop := PhaseCriterion (chartPhase s δ)
instance (s : State) (δ : Fin 4) : Decidable (phaseTest s δ) := inferInstanceAs (Decidable (PhaseCriterion _))

end Holant.Certificates.FourthRootOdd
