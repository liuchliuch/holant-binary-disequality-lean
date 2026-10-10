import Holant.Pauli.ExoticKlein.SixPortSymmetryTransport

/-! The six actual paired endpoint dressings in the physical stabilizer of
the distinguished E0⊗E0 card. Their scalar factors remain in the transported
complex coefficients. -/
namespace Holant.Pauli.ExoticKlein.SixPort
noncomputable section
set_option backward.isDefEq.respectTransparency false

 def localResidualAction (p : Fin 4) (a : Label) : ResidualAction where
  direction := localDirectionPerm p a
  coefficient := localCoefficient p a
  coefficient_ne_zero := localCoefficient_nonzero p a
  quad := localAction p a
  full := localAction p.succ.succ a
  quad_zero := localMatrix_zero p (E a)
  quad_scale h s := localMatrix_scale_tensor p s (E a) h
  quad_direction := localAction_direction p a
  cards h b := baseCard_local_remaining p a b h
  safe h hs := allPhysicalSafe_localAction h hs p.succ.succ a
  nonzero h hn := localAction_ne_zero p.succ.succ a h hn
  descend h hp := isProduct_of_localAction h p.succ.succ a hp

 def pairedLeftPort (g : Fin 6) : Fin 4 := if g.val < 3 then 0 else 2
 def pairedRightPort (g : Fin 6) : Fin 4 := if g.val < 3 then 1 else 3
 def pairedLeftLabel (g : Fin 6) : Label := ![xLabel,yLabel,zLabel] (Fin.ofNat 3 g.val)
 def pairedRightLabel (g : Fin 6) : Label := ![xLabel,zLabel,yLabel] (Fin.ofNat 3 g.val)

/-- Pure finite label permutation, independently executable for orbit checks. -/
 def pairedDirection (g : Fin 6) : Equiv.Perm Direction :=
  (localDirectionPerm (pairedLeftPort g) (pairedLeftLabel g)).trans
    (localDirectionPerm (pairedRightPort g) (pairedRightLabel g))

 def pairedAction (g : Fin 6) : ResidualAction :=
  (localResidualAction (pairedLeftPort g) (pairedLeftLabel g)).compose
    (localResidualAction (pairedRightPort g) (pairedRightLabel g))

 theorem pairedAction_direction (g : Fin 6) : (pairedAction g).direction = pairedDirection g := rfl

 theorem pairedDirection_fixes_base (g : Fin 6) : pairedDirection g baseDirection = baseDirection := by
  revert g
  decide +kernel

 theorem pairedDirection_involutive (g : Fin 6) : Function.Involutive (pairedDirection g) := by
  revert g
  unfold Function.Involutive
  decide +kernel

 def pairedState (g : Fin 6) (state : DirectionTriple) : DirectionTriple :=
  fun j => (state j).map (pairedDirection g)

 theorem pairedState_involutive (g : Fin 6) : Function.Involutive (pairedState g) := by
  intro state
  funext j
  cases h : state j with
  | none => simp [pairedState,h]
  | some d =>
    simp only [pairedState,h,Option.map_some]
    exact congrArg some (pairedDirection_involutive g d)

 theorem paired_solved_back (g : Fin 6) (state : DirectionTriple) (hs : Solved (pairedState g state)) : Solved state :=
  (pairedAction g).solved_back (pairedDirection_fixes_base g) state hs

 theorem paired_solved_iff (g : Fin 6) (state : DirectionTriple) : Solved (pairedState g state) ↔ Solved state := by
  constructor
  · exact paired_solved_back g state
  · intro hs
    apply paired_solved_back g (pairedState g state)
    rwa [pairedState_involutive]

end
end Holant.Pauli.ExoticKlein.SixPort
