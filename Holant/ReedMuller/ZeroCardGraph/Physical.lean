import Holant.ReedMuller.ZeroCardGraph.Elimination
import Holant.ReedMuller.CoefficientAtlas.Physical
import Holant.Dihedral.TwoCardLocalization.ResidualOrder

/-! Arbitrary-arity physical I/X closures and the exact Walsh card-pencil
identities. Original deleted ports and the residual incidence order remain
explicit; no analytic basis transformation is asserted to be a gadget. -/
noncomputable section
namespace Holant.ReedMuller.ZeroCardGraph
open Holant Holant.ReedMuller.CoefficientAtlas
open Holant.Dihedral.CompatibleClosure Holant.Dihedral.CompatibleCoefficientLine
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

 def physicalCard (f : Signature ℂ (n+2)) (o : Equiv.Perm (Fin (n+2))) (minus : Bool) : Signature ℂ n :=
  Signature.contract (if minus then Signature.disequality else Signature.equality) (Tensor.reindex o.symm f)

 def orderedCard (q : Signature ℂ (n+2)) (o : Equiv.Perm (Fin (n+2))) (minus : Bool) : Signature ℂ n :=
  fun y => 2*(q (fun i => pair false false y (o.symm i))+
    (if minus then -1 else 1)*q (fun i => pair true true y (o.symm i)))

 theorem walsh_closing_kernel (minus : Bool) :
    Kernel.pullback (if minus then (Signature.disequality : Kernel ℂ) else Signature.equality) walshKernel=
      fun a b => if a=b then 2*(if minus && a then -1 else 1) else 0 := by
  funext a b
  cases minus <;> cases a <;> cases b <;>
    norm_num [Kernel.pullback,Kernel.mul,Kernel.transpose,walshKernel,Signature.equality,Signature.disequality]

 theorem orderedCard_contract (q : Signature ℂ (n+2)) (o : Equiv.Perm (Fin (n+2))) (minus : Bool) :
    orderedCard q o minus=Signature.contract
      (Kernel.pullback (if minus then Signature.disequality else Signature.equality) walshKernel)
      (Tensor.reindex o.symm q) := by
  rw [walsh_closing_kernel]
  funext y
  cases minus <;> simp [orderedCard,Signature.contract,Tensor.reindex,Fintype.sum_bool,pair] <;> ring

 theorem walsh_physical_card (f : Signature ℂ (n+2)) (o : Equiv.Perm (Fin (n+2))) (minus : Bool) :
    walsh (physicalCard f o minus)=orderedCard (walsh f) o minus := by
  have he : physicalCard f o minus=
      Signature.coordinateAction (fun _ => walshKernel) (orderedCard (walsh f) o minus) := by
    unfold physicalCard
    conv_lhs => rw [←physical_of_walsh f]
    rw [←CoefficientAtlas.coordinateAction_reindex,coordinateAction_contract,←orderedCard_contract]
  rw [he,walsh_of_physical]

 theorem walsh_nonzero {N : ℕ} (f : Signature ℂ N) (hf : f ≠ 0) : walsh f ≠ 0 := by
  intro hz
  apply hf
  have hh := physical_of_walsh f
  rw [hz,Signature.coordinateAction_zero] at hh
  exact hh.symm

 theorem walsh_smul {N : ℕ} (c : ℂ) (f : Signature ℂ N) : walsh (c • f)=c • walsh f := by
  funext x
  simp only [walsh,Signature.coordinateAction,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

 def residualOrder (i j : Fin (n+2)) (hij : i ≠ j) : Fin n ≃ Remaining i j :=
  Holant.Dihedral.TwoCardLocalization.remainingOrder i j hij

 theorem sameLift_ordered (i j : Fin (n+2)) (hij : i ≠ j) (b : Bool)
    (y : Remaining i j → Bool) :
    sameLift i j b y=fun k => pair b b (fun r => y (residualOrder i j hij r)) ((pairOrder i j).symm k) := by
  funext k
  obtain ⟨l,rfl⟩ := (pairOrder i j).surjective k
  rw [Equiv.symm_apply_apply]
  refine Fin.cases ?_ (fun a => Fin.cases ?_ (fun r => ?_) a) l
  · rw [pairOrder_first i j hij,sameLift_left]
    rfl
  · change sameLift i j b y (pairOrder i j 1)=_
    rw [pairOrder_second,sameLift_right]
    rfl
  · change sameLift i j b y (residualOrder i j hij r).val=y (residualOrder i j hij r)
    exact sameLift_remaining _ _ _ _ _

 theorem card_named_ordered (q : Signature ℂ (n+2)) (i j : Fin (n+2)) (hij : i ≠ j) (minus : Bool) :
    card q i j minus=Tensor.reindex (residualOrder i j hij) (orderedCard q (pairOrder i j) minus) := by
  funext y
  simp only [card,Tensor.reindex,orderedCard,sameLift_ordered i j hij]

/-- Actual nonzero card-at-zero statements in the ordered deck imply exactly
the named-port hypothesis used by the graph elimination theorem. -/
 theorem nonzeroAtZero_of_physical (f : Signature ℂ (n+2))
    (hs : ∀ o : Equiv.Perm (Fin (n+2)),∀ minus : Bool,
      walsh (physicalCard f o minus) ≠ 0 → walsh (physicalCard f o minus) (fun _ => false) ≠ 0) :
    NonzeroAtZeroCards (walsh f) := by
  intro i j hij minus hn
  rw [card_named_ordered _ i j hij minus] at hn ⊢
  have hordered : orderedCard (walsh f) (pairOrder i j) minus ≠ 0 := by
    intro hz
    apply hn
    rw [hz]
    rfl
  have hh := hs (pairOrder i j) minus (by rwa [walsh_physical_card])
  simpa only [walsh_physical_card,Tensor.reindex] using hh

end Holant.ReedMuller.ZeroCardGraph
