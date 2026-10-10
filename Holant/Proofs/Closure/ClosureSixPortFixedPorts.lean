import Holant.Proofs.Closure.ClosureSixPortFixed

/-! Exact adapter from the root-pencil's ordered two-edge port equivalence
to the literal Z/C proper split. No port order or coefficient is re-chosen. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSixPort
open Holant
open Holant.LocalDrafts.FinitePGL2.Stabilization

def rulingPortsOrder (ports : (Fin 2 × Bool) ≃ Fin 4) : Equiv.Perm (Fin 4) :=
  finProdFinEquiv.symm.trans ((Equiv.prodCongr (Equiv.refl (Fin 2)) finTwoEquiv).trans ports)

@[simp] theorem rulingPorts_zero (ports : (Fin 2 × Bool) ≃ Fin 4) :
    rulingPortsOrder ports 0 = ports (0,false) := rfl
@[simp] theorem rulingPorts_one (ports : (Fin 2 × Bool) ≃ Fin 4) :
    rulingPortsOrder ports 1 = ports (0,true) := rfl
@[simp] theorem rulingPorts_two (ports : (Fin 2 × Bool) ≃ Fin 4) :
    rulingPortsOrder ports 2 = ports (1,false) := rfl
@[simp] theorem rulingPorts_three (ports : (Fin 2 × Bool) ≃ Fin 4) :
    rulingPortsOrder ports 3 = ports (1,true) := rfl

def commonResidualOfPorts (h : Signature ℂ 6) (e : Equiv.Perm (Fin 6)) (p : Bool)
    (ports : (Fin 2 × Bool) ≃ Fin 4) (fixed : Mat) (varying : Bool → Mat)
    (endpoints : ∀ a x, sliceSix h e p a x =
      fixed (x (ports (0,false))) (x (ports (0,true))) *
        varying a (x (ports (1,false))) (x (ports (1,true)))) : CommonResidualFactor h e p where
  order := rulingPortsOrder ports
  fixed := fixed
  varying := varying
  endpoints := by
    intro a x
    simpa only [rulingPorts_zero,rulingPorts_one,rulingPorts_two,rulingPorts_three] using endpoints a x

/-- The SAME root-pencil fixed factor gives the actual Z/C split in its
original residual port order. Both kernel parity orientations are included. -/
def zero_fixed_ports_split (h : Signature ℂ 6) (e : Equiv.Perm (Fin 6)) (p : Bool)
    (zero : ZeroSector h e (!p))
    (ports : (Fin 2 × Bool) ≃ Fin 4) (fixed : Mat) (varying : Bool → Mat)
    (endpoints : ∀ a x, sliceSix h e p a x =
      fixed (x (ports (0,false))) (x (ports (0,true))) *
        varying a (x (ports (1,false))) (x (ports (1,true)))) :
    ProperSplit (⟨6,h⟩ : AnySignature ℂ) ⟨2,binaryWord fixed⟩
      ⟨4,(commonResidualOfPorts h e p ports fixed varying endpoints).remainder⟩ :=
  zero_fixed_split h e p zero (commonResidualOfPorts h e p ports fixed varying endpoints)

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSixPort
