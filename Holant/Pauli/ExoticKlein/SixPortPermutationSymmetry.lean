import Holant.Pauli.ExoticKlein.SixPortPairedSymmetry

/-! The three actual residual port permutations in the base-card stabilizer.
Their direction permutations and scalar factors are derived from the literal
oriented matching tensors. -/
namespace Holant.Pauli.ExoticKlein.SixPort
noncomputable section
set_option backward.isDefEq.respectTransparency false

 def permutedDirection (e : Equiv.Perm (Fin 4)) (d : Direction) : Direction :=
  canonicalDirection (fun p => e (fourPort d.1 p.1 p.2)) (quadLabels d)

 def permutedCoefficient (e : Equiv.Perm (Fin 4)) (d : Direction) : ℂ :=
  Algebraic.gaussianToComplex (canonicalScalar (fun p => e (fourPort d.1 p.1 p.2)) (quadLabels d))

 theorem permutedCoefficient_nonzero (e : Equiv.Perm (Fin 4)) (d : Direction) : permutedCoefficient e d ≠ 0 :=
  (map_ne_zero Algebraic.gaussianToComplex).mpr (canonicalScalar_nonzero _ _)

 theorem reindex_direction (e : Equiv.Perm (Fin 4)) (d : Direction) :
    Tensor.reindex e (directionTensor d) =
      fun x => permutedCoefficient e d*directionTensor (permutedDirection e d) x := by
  rw [directionTensor_matching]
  funext x
  have hp : Function.Bijective (fun p : Fin 2 × Bool => e (fourPort d.1 p.1 p.2)) :=
    e.bijective.comp (fourMatching d.1).ports.bijective
  have hports (p : Fin 2 × Bool) : (fourMatching d.1).ports p = fourPort d.1 p.1 p.2 := rfl
  have h := congrArg Algebraic.gaussianToComplex
    (canonical_gaussian_matching (fun p => e (fourPort d.1 p.1 p.2)) hp (quadLabels d) x)
  simpa only [Tensor.reindex,Matching.tensor,hports,permutedCoefficient,permutedDirection,
    quadLabels,map_prod,map_mul,map_gaussianE,map_gaussianDirection] using h

 def residualPermutation (g : Fin 3) : Equiv.Perm (Fin 4) :=
  if g = 0 then Equiv.swap 0 1
  else if g = 1 then Equiv.swap 2 3
  else (Equiv.swap 0 2).trans (Equiv.swap 1 3)

 theorem permutedDirection_involutive (g : Fin 3) : Function.Involutive (permutedDirection (residualPermutation g)) := by
  revert g
  unfold Function.Involutive
  decide +kernel

 def permutationDirection (g : Fin 3) : Equiv.Perm Direction :=
  (permutedDirection_involutive g).toPerm

 theorem permutationDirection_fixes_base (g : Fin 3) : permutationDirection g baseDirection = baseDirection := by
  revert g
  decide +kernel

 def permutationAction (g : Fin 3) : ResidualAction where
  direction := permutationDirection g
  coefficient := permutedCoefficient (residualPermutation g)
  coefficient_ne_zero := permutedCoefficient_nonzero _
  quad := Tensor.reindex (residualPermutation g)
  full := Tensor.reindex (extendResidual (residualPermutation g))
  quad_zero := rfl
  quad_scale _ _ := rfl
  quad_direction := reindex_direction _
  cards h a := baseCard_reindex_residual _ a h
  safe h hs := allPhysicalSafe_reindex _ h hs
  nonzero h hn := reindex_ne_zero _ h hn
  descend h hp := isProduct_of_reindex _ h hp

end
end Holant.Pauli.ExoticKlein.SixPort
