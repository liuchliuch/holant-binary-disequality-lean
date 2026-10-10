import Holant.Certificates.FourthRootOdd.ExceptionalData
namespace Holant.Certificates.FourthRootOdd
open Holant Holant.Certificates.TwelveLoops
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000

theorem exceptional_parameter_remaining : ∀ x : AState, ∀ e : Bool,
    oddProduct x → classify (exceptionalState x e)=.remaining := by decide

theorem exceptional_parameter_coefficients : ∀ x : AState, ∀ e : Bool, oddProduct x →
    (∀ j : Fin 4, b (exceptionalState x e) j=gmul (fourthRoot (signPhase e)) (a (exceptionalState x e) j)) ∧
    (gmul (gmul (a (exceptionalState x e) 0) (a (exceptionalState x e) 1))
      (gmul (a (exceptionalState x e) 2) (a (exceptionalState x e) 3))=(0,1) ∨
     gmul (gmul (a (exceptionalState x e) 0) (a (exceptionalState x e) 1))
      (gmul (a (exceptionalState x e) 2) (a (exceptionalState x e) 3))=(0,-1)) := by decide

theorem exceptional_parameter_twoCopy : ∀ x : AState, ∀ e : Bool, oddProduct x →
    ((Finset.univ : Finset (Fin 4 → Bool)).filter
      (fun y => exactTwoCopy (exceptionalState x e) 0 y≠(0,0))).card=6 ∧
    exactTwoCopy (exceptionalState x e) 0 (fun _ => false)≠(0,0) ∧
    exactTwoCopy (exceptionalState x e) 0 (fun _ => true)≠(0,0) := by decide

end Holant.Certificates.FourthRootOdd
