import Holant.Pauli.ExoticKlein.SixPortCardAction

/-! Physical port permutations and reversed pair orders preserve the exact
safe-card condition, with nonzero transpose factors retained. -/
namespace Holant.Pauli.ExoticKlein.SixPort
noncomputable section
open scoped BigOperators
open ProjectiveDetermination

 def swapRest (r s : Fin 6) : Rest r s ≃ Rest s r where
  toFun i := ⟨i.val,i.property.2,i.property.1⟩
  invFun i := ⟨i.val,i.property.2,i.property.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

 theorem swap_fill (r s : Fin 6) (hr : r ≠ s) (u v : Bool) (z : Rest r s → Bool) :
    fill r s u v z = fill s r v u (fun j => z (swapRest s r j)) := by
  funext i
  by_cases hir : i = r
  · subst i; simp [fill,hr,Ne.symm hr]
  · by_cases his : i = s
    · subst i; simp [fill,hir]
    · simp [fill,hir,his,swapRest]

 theorem kernelCard_swap (r s : Fin 6) (hr : r ≠ s) (K : Mat) (h : Signature ℂ 6) :
    kernelCard r s K h = Tensor.reindex (swapRest s r) (kernelCard s r (Kernel.transpose K) h) := by
  funext z
  simp only [kernelCard,Tensor.reindex,Kernel.transpose_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  apply Finset.sum_congr rfl
  intro u hu
  rw [swap_fill r s hr u v z]

 theorem dual_transpose_scalar (a : Label) :
    ∃ c : ℂ, c ≠ 0 ∧ Kernel.transpose (dual a) = scale c (dual (theta a)) := by
  apply represents_dual_scalar
  exact (represents_dual a).transpose

 theorem matching_card_swap (r s : Fin 6) (hr : r ≠ s) (a : Label) (h : Signature ℂ 6)
    (hh : OnMatching (physicalCard s r (theta a) h)) : OnMatching (physicalCard r s a h) := by
  change OnMatching (kernelCard r s (dual a) h)
  rw [kernelCard_swap r s hr]
  obtain ⟨c,hc,he⟩ := dual_transpose_scalar a
  rw [he,kernelCard_scale]
  exact onMatching_reindex _ _ (onMatching_scale _ hh c)

 theorem AllPhysicalSafe.card_ne (h : Signature ℂ 6) (hh : AllPhysicalSafe h)
    (r s : Fin 6) (hr : r ≠ s) (a : Label) : OnMatching (physicalCard r s a h) := by
  rcases lt_or_gt_of_ne hr with hrs | hsr
  · exact hh r s hrs a
  · exact matching_card_swap r s hr a h (hh s r hsr (theta a))

 def restReindex (e : Equiv.Perm (Fin 6)) (r s : Fin 6) : Rest r s ≃ Rest (e r) (e s) where
  toFun i := ⟨e i.val,fun h => i.property.1 (e.injective h),fun h => i.property.2 (e.injective h)⟩
  invFun i := ⟨e.symm i.val,fun h => i.property.1 ((e.apply_symm_apply i.val).symm.trans (congrArg e h)),
    fun h => i.property.2 ((e.apply_symm_apply i.val).symm.trans (congrArg e h))⟩
  left_inv i := Subtype.ext (e.symm_apply_apply i.val)
  right_inv i := Subtype.ext (e.apply_symm_apply i.val)

 theorem fill_reindex (e : Equiv.Perm (Fin 6)) (r s : Fin 6) (u v : Bool)
    (z : Rest (e r) (e s) → Bool) :
    (fun i => fill (e r) (e s) u v z (e i)) = fill r s u v (fun j => z (restReindex e r s j)) := by
  funext i
  by_cases hir : i = r
  · subst i; simp [fill]
  · by_cases his : i = s
    · subst i; simp [fill,hir]
    · simp [fill,hir,his,restReindex]

 theorem physicalCard_reindex (e : Equiv.Perm (Fin 6)) (r s : Fin 6) (a : Label) (h : Signature ℂ 6) :
    physicalCard (e r) (e s) a (Tensor.reindex e h) =
      Tensor.reindex (restReindex e r s) (physicalCard r s a h) := by
  funext z
  simp only [physicalCard,Tensor.reindex,fill_reindex]

 theorem allPhysicalSafe_reindex (e : Equiv.Perm (Fin 6)) (h : Signature ℂ 6) (hh : AllPhysicalSafe h) :
    AllPhysicalSafe (Tensor.reindex e h) := by
  intro r s hrs a
  obtain ⟨r,rfl⟩ := e.surjective r
  obtain ⟨s,rfl⟩ := e.surjective s
  have hr : r ≠ s := fun he => ne_of_lt hrs (congrArg e he)
  rw [physicalCard_reindex]
  exact onMatching_reindex _ _ (AllPhysicalSafe.card_ne h hh r s hr a)

 theorem isProduct_reindex (e : Equiv.Perm (Fin 6)) (h : Signature ℂ 6) (hh : IsProduct h) :
    IsProduct (Tensor.reindex e h) := by
  obtain ⟨M,labels,s,hs,rfl⟩ := hh
  exact ⟨⟨M.ports.trans e⟩,labels,s,hs,rfl⟩

end
end Holant.Pauli.ExoticKlein.SixPort
