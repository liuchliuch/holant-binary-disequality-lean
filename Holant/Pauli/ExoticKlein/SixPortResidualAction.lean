import Holant.Pauli.ExoticKlein.SixPortReindex
import Holant.Pauli.ExoticKlein.SixPortPreparedForm

/-! Exact transport of the normalized base card under residual actions and
permutations, preserving all physical safe cards. -/
namespace Holant.Pauli.ExoticKlein.SixPort
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
open ProjectiveDetermination

 theorem localMatrix_reindex {P R : Type*} [DecidableEq P] [DecidableEq R]
    (e : P ≃ R) (p : P) (A : Mat) (h : Tensor ℂ P) :
    localMatrix (e p) A (Tensor.reindex e h) = Tensor.reindex e (localMatrix p A h) := by
  have hupdate (x : R → Bool) (u : Bool) :
      (fun q => Function.update x (e p) u (e q)) = Function.update (fun q => x (e q)) p u := by
    funext q
    by_cases hq : q = p
    · subst q; simp
    · have he : e q ≠ e p := fun he => hq (e.injective he)
      simp [Function.update_of_ne hq,Function.update_of_ne he]
  funext x
  simp only [localMatrix,Tensor.reindex,hupdate]

 theorem baseCard_as_reindex (a : Label) (h : Signature ℂ 6) :
    Tensor.reindex (remainingEquiv 0).symm (physicalCard 0 1 a h) = baseCard a h :=
  (card_as_physical_reindex 0 a h).symm.trans (card_base a h)

 theorem baseCard_local_first (a b : Label) (h : Signature ℂ 6) :
    ∃ c : ℂ, c ≠ 0 ∧ baseCard b (localAction 0 a h) = fun z => c*baseCard (a+b) h z := by
  obtain ⟨c,hc,he⟩ := left_dual_action a b
  refine ⟨c,hc,?_⟩
  have hk : physicalCard 0 1 b (localAction 0 a h) = fun z => c*physicalCard 0 1 (a+b) h z := by
    change kernelCard 0 1 (dual b) (localMatrix 0 (E a) h) = _
    rw [kernelCard_local_left 0 1 (by decide),he,kernelCard_scale]
    rfl
  have hh := congrArg (Tensor.reindex (remainingEquiv 0).symm) hk
  rw [baseCard_as_reindex] at hh
  change baseCard b (localAction 0 a h) = fun z => c*Tensor.reindex (remainingEquiv 0).symm (physicalCard 0 1 (a+b) h) z at hh
  rwa [baseCard_as_reindex] at hh

 theorem remainingPort_base (i : Fin 4) : remainingPort 0 i = i.succ.succ := by
  fin_cases i <;> rfl

 theorem baseCard_local_remaining (i : Fin 4) (a b : Label) (h : Signature ℂ 6) :
    baseCard b (localAction i.succ.succ a h) = localAction i a (baseCard b h) := by
  let q := remainingEquiv 0 i
  have hq : q.val = i.succ.succ := remainingPort_base i
  have hk := kernelCard_local_remaining 0 1 (dual b) (E a) h q
  have hh := congrArg (Tensor.reindex (remainingEquiv 0).symm) hk
  change Tensor.reindex (remainingEquiv 0).symm (physicalCard 0 1 b (localAction q.val a h)) =
    Tensor.reindex (remainingEquiv 0).symm (localMatrix q (E a) (physicalCard 0 1 b h)) at hh
  rw [hq,baseCard_as_reindex,← localMatrix_reindex] at hh
  have hi : (remainingEquiv 0).symm q = i := (remainingEquiv 0).symm_apply_apply i
  rw [hi,baseCard_as_reindex] at hh
  exact hh

 def extendResidual (e : Equiv.Perm (Fin 4)) : Equiv.Perm (Fin 6) :=
  (finSumFinEquiv (m := 2) (n := 4)).symm.trans
    ((Equiv.sumCongr (Equiv.refl (Fin 2)) e).trans (finSumFinEquiv (m := 2) (n := 4)))

@[simp] theorem extendResidual_zero (e : Equiv.Perm (Fin 4)) : extendResidual e 0 = 0 := rfl
@[simp] theorem extendResidual_one (e : Equiv.Perm (Fin 4)) : extendResidual e 1 = 1 := rfl

 theorem extendResidual_tail (e : Equiv.Perm (Fin 4)) (i : Fin 4) :
    extendResidual e i.succ.succ = (e i).succ.succ := by
  have hi : i.succ.succ = (finSumFinEquiv (m := 2) (n := 4)) (.inr i) := by apply Fin.ext; change i.val+1+1 = 2+i.val; omega
  have he : (e i).succ.succ = (finSumFinEquiv (m := 2) (n := 4)) (.inr (e i)) := by apply Fin.ext; change (e i).val+1+1 = 2+(e i).val; omega
  rw [hi,he]
  simp [extendResidual]

 theorem extendResidual_fill (e : Equiv.Perm (Fin 4)) (u v : Bool) (z : Fin 4 → Bool) :
    (fun i : Fin 6 => (Fin.cons u (Fin.cons v z) : Fin 6 → Bool) (extendResidual e i)) =
      (Fin.cons u (Fin.cons v (fun j : Fin 4 => z (e j))) : Fin 6 → Bool) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · refine Fin.cases ?_ (fun j => ?_) j
    · simp
    · rw [extendResidual_tail]
      rfl

 theorem baseCard_reindex_residual (e : Equiv.Perm (Fin 4)) (a : Label) (h : Signature ℂ 6) :
    baseCard a (Tensor.reindex (extendResidual e) h) = Tensor.reindex e (baseCard a h) := by
  funext z
  simp only [baseCard,Tensor.reindex,extendResidual_fill]

 def straightenMatching (m : Fin 3) : Equiv.Perm (Fin 4) :=
  (fourMatching m).ports.symm.trans (fourMatching 0).ports

 theorem straighten_direction (m : Fin 3) (a b : Label) :
    Tensor.reindex (straightenMatching m) (directionTensor (m,a,b)) = directionTensor (0,a,b) := by
  rw [directionTensor_matching,directionTensor_matching]
  funext x
  simp only [Tensor.reindex,Matching.tensor,straightenMatching,Equiv.trans_apply,Equiv.symm_apply_apply]

 theorem baseCard_scale (a : Label) (h : Signature ℂ 6) (s : ℂ) :
    baseCard a (fun x => s*h x) = fun z => s*baseCard a h z := by
  funext z
  simp only [baseCard,Fintype.sum_bool]
  ring

 theorem allPhysicalSafe_scale (h : Signature ℂ 6) (hh : AllPhysicalSafe h) (c : ℂ) :
    AllPhysicalSafe (fun x => c*h x) := by
  intro r s hrs a
  have he : physicalCard r s a (fun x => c*h x) = fun z => c*physicalCard r s a h z := by
    funext z
    simp only [physicalCard,Fintype.sum_bool]
    ring
  rw [he]
  exact onMatching_scale _ (hh r s hrs a) c

 theorem isProduct_scale (h : Signature ℂ 6) (hh : IsProduct h) (c : ℂ) (hc : c ≠ 0) :
    IsProduct (fun x => c*h x) := by
  obtain ⟨M,labels,s,hs,rfl⟩ := hh
  exact ⟨M,labels,c*s,mul_ne_zero hc hs,by funext x; ring⟩

 theorem isProduct_localAction (h : Signature ℂ 6) (hh : IsProduct h) (p : Fin 6) (a : Label) :
    IsProduct (localAction p a h) := by
  obtain ⟨M,labels,s,hs,rfl⟩ := hh
  obtain ⟨labels',t,ht,he⟩ := localAction_matching M labels p a
  refine ⟨M,labels',s*t,mul_ne_zero hs ht,?_⟩
  unfold localAction at he ⊢
  rw [localMatrix_scale_tensor,he]
  funext x
  ring

end
end Holant.Pauli.ExoticKlein.SixPort
