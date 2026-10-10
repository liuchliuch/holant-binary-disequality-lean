import Holant.Pauli.ExoticKlein.SixPortResidualAction

/-! Exact normalization and descent identities for the distinguished base card. -/
namespace Holant.Pauli.ExoticKlein.SixPort
noncomputable section
set_option backward.isDefEq.respectTransparency false

 theorem reindex_ne_zero (e : Equiv.Perm (Fin 6)) (h : Signature ℂ 6) (hn : h ≠ 0) :
    Tensor.reindex e h ≠ 0 := by
  intro hz
  apply hn
  funext x
  have hx := congrFun hz (fun i => x (e.symm i))
  simpa only [Tensor.reindex,Equiv.symm_apply_apply,Pi.zero_apply] using hx

 theorem scale_ne_zero (h : Signature ℂ 6) (hn : h ≠ 0) (c : ℂ) (hc : c ≠ 0) :
    (fun x => c*h x) ≠ (0 : Signature ℂ 6) := by
  intro hz
  apply hn
  funext x
  have hx := congrFun hz x
  change c*h x = 0 at hx
  exact (mul_eq_zero.mp hx).resolve_left hc

 theorem isProduct_of_scale (h : Signature ℂ 6) (c : ℂ) (hc : c ≠ 0)
    (hp : IsProduct (fun x => c*h x)) : IsProduct h := by
  have hh := isProduct_scale _ hp c⁻¹ (inv_ne_zero hc)
  have he : (fun x => c⁻¹*(c*h x)) = h := by
    funext x
    rw [← mul_assoc,inv_mul_cancel₀ hc,one_mul]
  rwa [he] at hh

 theorem isProduct_of_localAction (h : Signature ℂ 6) (p : Fin 6) (a : Label)
    (hp : IsProduct (localAction p a h)) : IsProduct h := by
  have hh := isProduct_localAction _
    (isProduct_scale _ hp (omega a a)⁻¹ (inv_ne_zero (omega_ne_zero a a))) p a
  rwa [localAction_inverse] at hh

 theorem isProduct_of_reindex (e : Equiv.Perm (Fin 6)) (h : Signature ℂ 6)
    (hp : IsProduct (Tensor.reindex e h)) : IsProduct h := by
  have hh := isProduct_reindex e.symm _ hp
  have he : Tensor.reindex e.symm (Tensor.reindex e h) = h := by
    funext x
    simp only [Tensor.reindex,Equiv.symm_apply_apply]
  rwa [he] at hh

 theorem base_cancel_first (a b : Label) :
    localAction (0 : Fin 4) a (directionTensor (0,a,b)) =
      fun z => omega a a*directionTensor (0,0,b) z := by
  rw [directionTensor_matching,directionTensor_matching]
  have h := localAction_matching_first (fourMatching 0) ![a,b] (0 : Fin 2) a
  change localAction 0 a ((fourMatching 0).tensor ![a,b]) =
    (fun z => omega a a*(fourMatching 0).tensor (Function.update ![a,b] 0 (a+a)) z) at h
  have hu : Function.update ![a,b] (0 : Fin 2) (a+a) = ![0,b] := by
    funext i
    fin_cases i <;> simp [label_add_self]
  rwa [hu] at h

 theorem base_cancel_second (a b : Label) :
    localAction (2 : Fin 4) b (directionTensor (0,a,b)) =
      fun z => omega b b*directionTensor (0,a,0) z := by
  rw [directionTensor_matching,directionTensor_matching]
  have h := localAction_matching_first (fourMatching 0) ![a,b] (1 : Fin 2) b
  change localAction 2 b ((fourMatching 0).tensor ![a,b]) =
    (fun z => omega b b*(fourMatching 0).tensor (Function.update ![a,b] 1 (b+b)) z) at h
  have hu : Function.update ![a,b] (1 : Fin 2) (b+b) = ![a,0] := by
    funext i
    fin_cases i <;> simp [label_add_self]
  rwa [hu] at h

 theorem baseCard_onDirection (h : Signature ℂ 6) (hs : AllPhysicalSafe h) (a : Label) :
    OnDirection (baseCard a h) := by
  rw [← card_base]
  exact (allPhysicalSafe_iff_ordered h).mp hs 0 a

end
end Holant.Pauli.ExoticKlein.SixPort
