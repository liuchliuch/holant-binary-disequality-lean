import Holant.Pauli.ExoticKlein.SixPortNormalization

/-! Computable action of a local exotic dressing on the forty-eight actual
quaternary directions, retaining its exact nonzero scalar. -/
namespace Holant.Pauli.ExoticKlein.SixPort
noncomputable section
set_option backward.isDefEq.respectTransparency false

 def fourPortInverse (m : Fin 3) (p : Fin 4) : Fin 2 × Bool :=
  if m = 0 then ![(0,false),(0,true),(1,false),(1,true)] p
  else if m = 1 then ![(0,false),(1,false),(0,true),(1,true)] p
  else ![(0,false),(1,false),(1,true),(0,true)] p

 theorem fourPort_inverse (m : Fin 3) (p : Fin 4) :
    fourPort m (fourPortInverse m p).1 (fourPortInverse m p).2 = p := by
  revert m p
  decide

 def quadLabels (d : Direction) : Fin 2 → Label := ![d.2.1,d.2.2]

 def localDirectionLabels (p : Fin 4) (a : Label) (d : Direction) : Fin 2 → Label :=
  let q := fourPortInverse d.1 p
  Function.update (quadLabels d) q.1
    (if q.2 then quadLabels d q.1+theta a else a+quadLabels d q.1)

 def localDirection (p : Fin 4) (a : Label) (d : Direction) : Direction :=
  (d.1,localDirectionLabels p a d 0,localDirectionLabels p a d 1)

 def localCoefficient (p : Fin 4) (a : Label) (d : Direction) : ℂ :=
  let q := fourPortInverse d.1 p
  if q.2 then transposeScalar a*omega (quadLabels d q.1) (theta a)
  else omega a (quadLabels d q.1)

 theorem localCoefficient_nonzero (p : Fin 4) (a : Label) (d : Direction) : localCoefficient p a d ≠ 0 := by
  dsimp only [localCoefficient]
  split
  · exact mul_ne_zero (transposeScalar_ne_zero _) (omega_ne_zero _ _)
  · exact omega_ne_zero _ _

 theorem localDirection_involutive (p : Fin 4) (a : Label) : Function.Involutive (localDirection p a) := by
  revert p a
  unfold Function.Involutive
  decide +kernel

 def localDirectionPerm (p : Fin 4) (a : Label) : Equiv.Perm Direction :=
  (localDirection_involutive p a).toPerm

 theorem quadLabels_eta (f : Fin 2 → Label) : ![f 0,f 1] = f := by
  funext i
  fin_cases i <;> rfl

 theorem localDirection_tensor (p : Fin 4) (a : Label) (d : Direction) :
    directionTensor (localDirection p a d) = (fourMatching d.1).tensor (localDirectionLabels p a d) := by
  rw [directionTensor_matching]
  change (fourMatching d.1).tensor ![localDirectionLabels p a d 0,localDirectionLabels p a d 1] = _
  rw [quadLabels_eta]

 theorem localAction_direction (p : Fin 4) (a : Label) (d : Direction) :
    localAction p a (directionTensor d) =
      fun x => localCoefficient p a d*directionTensor (localDirection p a d) x := by
  rw [localDirection_tensor,directionTensor_matching]
  change localAction p a ((fourMatching d.1).tensor (quadLabels d)) = _
  let q := fourPortInverse d.1 p
  have hp : (fourMatching d.1).ports (q.1,q.2) = p := fourPort_inverse d.1 p
  calc
    localAction p a ((fourMatching d.1).tensor (quadLabels d)) =
        localAction ((fourMatching d.1).ports (q.1,q.2)) a ((fourMatching d.1).tensor (quadLabels d)) := by rw [hp]
    _ = _ := by
      change localAction ((fourMatching d.1).ports (q.1,q.2)) a ((fourMatching d.1).tensor (quadLabels d)) =
        fun x => (if q.2 then transposeScalar a*omega (quadLabels d q.1) (theta a)
          else omega a (quadLabels d q.1))*
          (fourMatching d.1).tensor (Function.update (quadLabels d) q.1
            (if q.2 then quadLabels d q.1+theta a else a+quadLabels d q.1)) x
      cases hq : q.2
      · simp only [hq,Bool.false_eq_true,ite_false]
        exact localAction_matching_first _ _ _ _
      · simp only [hq,ite_true]
        exact localAction_matching_second _ _ _ _

end
end Holant.Pauli.ExoticKlein.SixPort
