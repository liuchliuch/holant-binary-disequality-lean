import Holant.Pauli.ExoticKlein.SixPortMatchingAction

/-! Literal commutation of pair contractions and local exotic actions. -/
namespace Holant.Pauli.ExoticKlein.SixPort
noncomputable section
open scoped BigOperators
open ProjectiveDetermination

 def kernelCard (r s : Fin 6) (K : Mat) (h : Signature ℂ 6) : Tensor ℂ (Rest r s) :=
  fun z => ∑ u : Bool, ∑ v : Bool, K u v*h (fill r s u v z)

 theorem update_fill_left (r s : Fin 6) (hr : r ≠ s) (u v t : Bool) (z : Rest r s → Bool) :
    Function.update (fill r s u v z) r t = fill r s t v z := by
  funext i
  by_cases hi : i = r
  · subst i; simp [fill]
  · by_cases hs : i = s
    · subst i; simp [fill,hi]
    · simp [fill,hi,hs,Function.update_of_ne hi]

 theorem update_fill_right (r s : Fin 6) (hr : r ≠ s) (u v t : Bool) (z : Rest r s → Bool) :
    Function.update (fill r s u v z) s t = fill r s u t z := by
  funext i
  by_cases hi : i = r
  · subst i; simp [fill,hr]
  · by_cases hs : i = s
    · subst i; simp [fill,hi]
    · simp [fill,hi,hs,Function.update_of_ne hs]

 theorem update_fill_remaining (r s : Fin 6) (u v t : Bool) (z : Rest r s → Bool) (p : Rest r s) :
    Function.update (fill r s u v z) p.val t = fill r s u v (Function.update z p t) := by
  funext i
  by_cases hi : i = r
  · subst i; simp [fill,p.property.1,Ne.symm p.property.1]
  · by_cases hs : i = s
    · subst i; simp [fill,hi,p.property.2,Ne.symm p.property.2]
    · by_cases hp : i = p.val
      · subst i; simp [fill,p.property.1,p.property.2]
      · have he : (⟨i,hi,hs⟩ : Rest r s) ≠ p := fun h => hp (congrArg Subtype.val h)
        simp [fill,hi,hs,Function.update_of_ne hp,Function.update_of_ne he]

 theorem kernelCard_local_left (r s : Fin 6) (hr : r ≠ s) (K A : Mat) (h : Signature ℂ 6) :
    kernelCard r s K (localMatrix r A h) = kernelCard r s (Kernel.mul (Kernel.transpose A) K) h := by
  funext z
  simp only [kernelCard,localMatrix,fill_left,update_fill_left r s hr,Fintype.sum_bool,Kernel.mul_apply,Kernel.transpose_apply]
  ring

 theorem kernelCard_local_right (r s : Fin 6) (hr : r ≠ s) (K A : Mat) (h : Signature ℂ 6) :
    kernelCard r s K (localMatrix s A h) = kernelCard r s (Kernel.mul K A) h := by
  funext z
  simp only [kernelCard,localMatrix,fill_right r s hr,update_fill_right r s hr,Fintype.sum_bool,Kernel.mul_apply]
  ring

 theorem kernelCard_local_remaining (r s : Fin 6) (K A : Mat) (h : Signature ℂ 6) (p : Rest r s) :
    kernelCard r s K (localMatrix p.val A h) = localMatrix p A (kernelCard r s K h) := by
  funext z
  simp only [kernelCard,localMatrix,fill_rest,update_fill_remaining,Fintype.sum_bool]
  ring

 theorem kernelCard_scale (r s : Fin 6) (K : Mat) (c : ℂ) (h : Signature ℂ 6) :
    kernelCard r s (scale c K) h = fun z => c*kernelCard r s K h z := by
  funext z
  simp only [kernelCard,scale,Fintype.sum_bool]
  ring

 theorem represents_dual_scalar (a : Label) (T : Mat) (h : Represents (theta a) T) :
    ∃ c : ℂ, c ≠ 0 ∧ T = scale c (dual a) := by
  obtain ⟨c,hc,he⟩ := h
  refine ⟨c*d a,mul_ne_zero hc (d_ne_zero a),?_⟩
  rw [he]
  funext x y
  simp [scale,dual_apply,mul_assoc,d_ne_zero]

 theorem left_dual_action (a b : Label) :
    ∃ c : ℂ, c ≠ 0 ∧ Kernel.mul (Kernel.transpose (E a)) (dual b) = scale c (dual (a+b)) := by
  apply represents_dual_scalar
  have h := (represents_E a).transpose.mul (represents_dual b)
  simpa only [theta_add] using h

 theorem right_dual_action (a b : Label) :
    ∃ c : ℂ, c ≠ 0 ∧ Kernel.mul (dual b) (E a) = scale c (dual (b+theta a)) := by
  apply represents_dual_scalar
  have h := (represents_dual b).mul (represents_E a)
  simpa only [theta_add,theta_theta] using h

 theorem onMatching_scale {P : Type*} (h : Tensor ℂ P) (hh : OnMatching h) (s : ℂ) :
    OnMatching (fun x => s*h x) := by
  by_cases hs : s = 0
  · left; subst s; funext x; simp
  · rcases hh with rfl | ⟨M,labels,t,ht,rfl⟩
    · left; funext x; simp
    · right
      exact ⟨M,labels,s*t,mul_ne_zero hs ht,by funext x; ring⟩

/-- All actual safe cards are preserved by a local exotic dressing, including
when the dressed port is one of the two deleted occurrences. -/
 theorem allPhysicalSafe_localAction (h : Signature ℂ 6) (hh : AllPhysicalSafe h) (p : Fin 6) (a : Label) :
    AllPhysicalSafe (localAction p a h) := by
  intro r s hrs b
  change OnMatching (kernelCard r s (dual b) (localMatrix p (E a) h))
  by_cases hpr : p = r
  · subst p
    rw [kernelCard_local_left r s (ne_of_lt hrs)]
    obtain ⟨c,hc,he⟩ := left_dual_action a b
    rw [he,kernelCard_scale]
    exact onMatching_scale _ (hh r s hrs (a+b)) c
  · by_cases hps : p = s
    · subst p
      rw [kernelCard_local_right r s (ne_of_lt hrs)]
      obtain ⟨c,hc,he⟩ := right_dual_action a b
      rw [he,kernelCard_scale]
      exact onMatching_scale _ (hh r s hrs (b+theta a)) c
    · let q : Rest r s := ⟨p,hpr,hps⟩
      change OnMatching (kernelCard r s (dual b) (localMatrix q.val (E a) h))
      rw [kernelCard_local_remaining]
      exact onMatching_localAction _ (hh r s hrs b) q a

end
end Holant.Pauli.ExoticKlein.SixPort
