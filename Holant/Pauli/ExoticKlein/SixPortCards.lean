import Holant.Pauli.ExoticKlein.SixPortSetup

/-! Literal original-port card matrices for all sixty six-port pair/kernel
contexts. Residual ports stay in increasing original order. -/
namespace Holant.Pauli.ExoticKlein.SixPort
noncomputable section
open scoped BigOperators
open ProjectiveDetermination

abbrev PortPair := {p : Fin 6 × Fin 6 // p.1 < p.2}

 def portPairs : Fin 15 → PortPair :=
  ![⟨(0,1),by decide⟩,⟨(0,2),by decide⟩,⟨(0,3),by decide⟩,⟨(0,4),by decide⟩,⟨(0,5),by decide⟩,
    ⟨(1,2),by decide⟩,⟨(1,3),by decide⟩,⟨(1,4),by decide⟩,⟨(1,5),by decide⟩,
    ⟨(2,3),by decide⟩,⟨(2,4),by decide⟩,⟨(2,5),by decide⟩,
    ⟨(3,4),by decide⟩,⟨(3,5),by decide⟩,⟨(4,5),by decide⟩]

 theorem portPairs_bijective : Function.Bijective portPairs := by decide

 def remainingPort : Fin 15 → Fin 4 → Fin 6 :=
  ![![2,3,4,5],![1,3,4,5],![1,2,4,5],![1,2,3,5],![1,2,3,4],
    ![0,3,4,5],![0,2,4,5],![0,2,3,5],![0,2,3,4],
    ![0,1,4,5],![0,1,3,5],![0,1,3,4],![0,1,2,5],![0,1,2,4],![0,1,2,3]]

 def remainingRank (p : Fin 15) (j : Fin 6) : Fin 4 :=
  Fin.ofNat 4 (j.val-(if (portPairs p).val.1 < j then 1 else 0)-(if (portPairs p).val.2 < j then 1 else 0))

 theorem remaining_ne (p : Fin 15) (i : Fin 4) :
    remainingPort p i ≠ (portPairs p).val.1 ∧ remainingPort p i ≠ (portPairs p).val.2 := by
  revert p i
  decide

 theorem remaining_rank_port (p : Fin 15) (i : Fin 4) : remainingRank p (remainingPort p i) = i := by
  revert p i
  decide

 theorem remaining_port_rank (p : Fin 15) (j : Fin 6)
    (h : j ≠ (portPairs p).val.1 ∧ j ≠ (portPairs p).val.2) :
    remainingPort p (remainingRank p j) = j := by
  revert p j h
  decide

/-- A computable equivalence with the physical complement of the two ports. -/
 def remainingEquiv (p : Fin 15) : Fin 4 ≃ Rest (portPairs p).val.1 (portPairs p).val.2 where
  toFun i := ⟨remainingPort p i,remaining_ne p i⟩
  invFun j := remainingRank p j.val
  left_inv i := remaining_rank_port p i
  right_inv j := Subtype.ext (remaining_port_rank p j.val j.property)

 def fillOrdered (p : Fin 15) (u v : Bool) (z : Fin 4 → Bool) : Fin 6 → Bool :=
  fill (portPairs p).val.1 (portPairs p).val.2 u v (fun j => z ((remainingEquiv p).symm j))

@[simp] theorem fillOrdered_left (p : Fin 15) (u v : Bool) (z : Fin 4 → Bool) :
    fillOrdered p u v z (portPairs p).val.1 = u := fill_left _ _ _ _ _

@[simp] theorem fillOrdered_right (p : Fin 15) (u v : Bool) (z : Fin 4 → Bool) :
    fillOrdered p u v z (portPairs p).val.2 = v :=
  fill_right _ _ (ne_of_lt (portPairs p).property) _ _ _

@[simp] theorem fillOrdered_remaining (p : Fin 15) (u v : Bool) (z : Fin 4 → Bool) (i : Fin 4) :
    fillOrdered p u v z (remainingPort p i) = z i := by
  change fill _ _ u v (fun j => z ((remainingEquiv p).symm j)) ((remainingEquiv p i).val) = _
  rw [fill_rest,Equiv.symm_apply_apply]

 def cardOver {K : Type*} [Field K] (imaginary : K) (p : Fin 15) (a : Label)
    (h : Signature K 6) : Signature K 4 :=
  fun z => ∑ u : Bool, ∑ v : Bool, dualOver imaginary a u v*h (fillOrdered p u v z)

 def card := cardOver Complex.I
 def gaussianCard := cardOver gaussianI

 theorem map_gaussianCard (p : Fin 15) (a : Label) (h : Signature LinearCertificate.Q 6)
    (z : Fin 4 → Bool) :
    Algebraic.gaussianToComplex (gaussianCard p a h z) =
      card p a (fun x => Algebraic.gaussianToComplex (h x)) z := by
  have hm (u v : Bool) : Algebraic.gaussianToComplex (dualOver gaussianI a u v) =
      dualOver Complex.I a u v := map_gaussianDual a u v
  simp only [gaussianCard,card,cardOver,map_sum,map_mul,hm]

 def gaussianTerm (state : DirectionTriple) (i : Fin 4) : Signature LinearCertificate.Q 6 :=
  fun x => gaussianE (labelEquiv i) (x 0) (x 1)*gaussianOptionDirection (cardDirections state i) (tail4 x)

 theorem map_gaussianTerm (state : DirectionTriple) (i : Fin 4) (x : Fin 6 → Bool) :
    Algebraic.gaussianToComplex (gaussianTerm state i x) =
      E (labelEquiv i) (x 0) (x 1)*optionDirection (cardDirections state i) (tail4 x) := by
  simp only [gaussianTerm,map_mul,map_gaussianE,map_gaussianOptionDirection]

 def contextEquiv : Fin 60 ≃ (Fin 15 × Fin 4) := (finProdFinEquiv (m := 15) (n := 4)).symm

 def cardMatrix (state : DirectionTriple) (context : Fin 60) : Fin 16 → LinearCertificate.Row 4 :=
  fun word i => gaussianCard (contextEquiv context).1 (labelEquiv (contextEquiv context).2)
    (gaussianTerm state i) ((wordEquiv 4).symm word)

 theorem card_normalizedTensor (state : DirectionTriple) (scale : Fin 4 → ℂ)
    (p : Fin 15) (a : Label) (z : Fin 4 → Bool) :
    card p a (normalizedTensor state scale) z =
      ∑ i : Fin 4, scale i*card p a (fun x => Algebraic.gaussianToComplex (gaussianTerm state i x)) z := by
  simp only [normalizedTensor,card,cardOver,map_gaussianTerm,Fintype.sum_bool,
    Fin.sum_univ_succ,Fin.sum_univ_zero]
  ring


 theorem cardMatrix_semantics (state : DirectionTriple) (scale : Fin 4 → ℂ)
    (context : Fin 60) (word : Fin 16) :
    LinearCertificate.output (cardMatrix state context) scale word =
      card (contextEquiv context).1 (labelEquiv (contextEquiv context).2)
        (normalizedTensor state scale) ((wordEquiv 4).symm word) := by
  rw [card_normalizedTensor]
  unfold LinearCertificate.output LinearCertificate.evaluate cardMatrix
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_gaussianCard]
  exact mul_comm _ _

end
end Holant.Pauli.ExoticKlein.SixPort
