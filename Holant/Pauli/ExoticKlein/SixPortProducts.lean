import Holant.Pauli.ExoticKlein.SixPortLines
import Holant.Pauli.ExoticKlein.Matching

/-! Literal product targets for the finite six-port certificate. Every target
is proved to be an actual oriented three-edge matching tensor. -/
namespace Holant.Pauli.ExoticKlein.SixPort
noncomputable section
open scoped BigOperators

abbrev ProductDirection := Fin 5 × Label × Direction

 def firstPair (j : Fin 5) : Fin 15 := j.castLE (by decide)

 theorem firstPair_value (j : Fin 5) : (portPairs (firstPair j)).val = (0,j.succ) := by
  revert j
  decide

 def productTensorOver {K : Type*} [Ring K] (imaginary : K) (d : ProductDirection) : Signature K 6 :=
  fun x => EOver imaginary d.2.1 (x 0) (x d.1.succ)*
    directionTensorOver imaginary d.2.2 (fun i => x (remainingPort (firstPair d.1) i))

 def productTensor := productTensorOver Complex.I
 def gaussianProduct := productTensorOver gaussianI

 theorem map_gaussianProduct (d : ProductDirection) (x : Fin 6 → Bool) :
    Algebraic.gaussianToComplex (gaussianProduct d x) = productTensor d x := by
  have hm (a : Label) (u v : Bool) : Algebraic.gaussianToComplex (EOver gaussianI a u v) =
      EOver Complex.I a u v := map_gaussianE a u v
  unfold gaussianProduct productTensor productTensorOver
  rw [map_mul,hm]
  exact congrArg (fun z => EOver Complex.I d.2.1 (x 0) (x d.1.succ)*z) (map_gaussianDirection _ _)

 def fourPort (m : Fin 3) (e : Fin 2) (b : Bool) : Fin 4 :=
  if m = 0 then (if e = 0 then (if b then 1 else 0) else (if b then 3 else 2))
  else if m = 1 then (if e = 0 then (if b then 2 else 0) else (if b then 3 else 1))
  else (if e = 0 then (if b then 3 else 0) else (if b then 2 else 1))

 def productPort (j : Fin 5) (m : Fin 3) (p : Fin 3 × Bool) : Fin 6 :=
  if p.1 = 0 then (if p.2 then j.succ else 0)
  else remainingPort (firstPair j) (fourPort m (Fin.ofNat 2 (p.1.val-1)) p.2)

 theorem productPort_bijective (j : Fin 5) (m : Fin 3) : Function.Bijective (productPort j m) := by
  revert j m
  decide +kernel

 def productMatching (j : Fin 5) (m : Fin 3) : Matching (Fin 6) 3 :=
  ⟨Equiv.ofBijective (productPort j m) (productPort_bijective j m)⟩

 def productLabels (d : ProductDirection) : Fin 3 → Label := ![d.2.1,d.2.2.2.1,d.2.2.2.2]

 theorem productTensor_matching (d : ProductDirection) :
    productTensor d = (productMatching d.1 d.2.2.1).tensor (productLabels d) := by
  rcases d with ⟨j,a,m,b,c⟩
  funext x
  fin_cases m <;>
    simp [productTensor,productTensorOver,directionTensorOver,Matching.tensor,productMatching,
      productPort,fourPort,productLabels,Fin.prod_univ_succ,E,mul_assoc]

 def productDirectionEquiv : Fin 960 ≃ ProductDirection :=
  (finProdFinEquiv (m := 5) (n := 192)).symm.trans
    (Equiv.prodCongr (Equiv.refl (Fin 5))
      ((finProdFinEquiv (m := 4) (n := 48)).symm.trans (Equiv.prodCongr labelEquiv directionEquiv)))

 def productWord (d : ProductDirection) : Fin 6 → Bool :=
  fillOrdered (firstPair d.1) false (decide (d.2.1 = xLabel)) (directionWord d.2.2)

 theorem gaussianProduct_pivot_nonzero (d : ProductDirection) : gaussianProduct d (productWord d) ≠ 0 := by
  have hp := firstPair_value d.1
  have hleft : (portPairs (firstPair d.1)).val.1 = 0 := congrArg Prod.fst hp
  have hright : (portPairs (firstPair d.1)).val.2 = d.1.succ := congrArg Prod.snd hp
  have hb (a : Label) : gaussianE a false (decide (a = xLabel)) ≠ 0 := by
    revert a
    decide +kernel
  unfold gaussianProduct productTensorOver productWord
  rw [← hleft,← hright,fillOrdered_left,fillOrdered_right]
  simp only [fillOrdered_remaining]
  exact mul_ne_zero (hb _) (gaussianDirection_pivot_nonzero _)

 def productVector (j : Fin 960) : Fin 64 → LinearCertificate.Q :=
  fun word => gaussianProduct (productDirectionEquiv j) ((wordEquiv 6).symm word)

 def productPivot (j : Fin 960) : Fin 64 := wordEquiv 6 (productWord (productDirectionEquiv j))

 theorem productPivot_nonzero (j : Fin 960) : productVector j (productPivot j) ≠ 0 := by
  simp only [productVector,productPivot,Equiv.symm_apply_apply]
  exact gaussianProduct_pivot_nonzero _

 theorem productVector_semantics (j : Fin 960) (word : Fin 64) :
    Algebraic.gaussianToComplex (productVector j word) =
      productTensor (productDirectionEquiv j) ((wordEquiv 6).symm word) := map_gaussianProduct _ _

end
end Holant.Pauli.ExoticKlein.SixPort
