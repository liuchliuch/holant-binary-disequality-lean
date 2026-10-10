import Holant.ReedMuller.SafeCollapse.Diagonal

/-! A safe one-port dressing of an actual RM deck has eigenvalue ratio ±1.
Both character statements come from the proved physical coefficient atlas. -/
namespace Holant.ReedMuller.SafeCollapse
open Holant Holant.ReedMuller.CoefficientAtlas Holant.ReedMuller.LowArity
noncomputable section
set_option backward.isDefEq.respectTransparency false

 theorem vector_zero_mem : vector (fun _ : Fin 8 => false)∈code := by
  change (0 : BinaryVector 8)∈code
  exact code.zero_mem

 theorem vector_one_mem : vector (fun _ : Fin 8 => true)∈code := by
  exact ⟨oneParam,evaluate_one⟩

 theorem endpoint_character (q : Signature ℂ 8) (hs : SupportRM (walsh q)) (hd : PhysicalDeck q) :
    walsh q (fun _ => false)≠0 ∧
      (walsh q (fun _ => true)=walsh q (fun _ => false) ∨
       walsh q (fun _ => true)= -walsh q (fun _ => false)) := by
  obtain ⟨c,w,hc,_,_⟩ := source_rm_coefficient_atlas q hs hd
  have h0 := hc (fun _ => false)
  have h1 := hc (fun _ => true)
  rw [if_pos vector_zero_mem] at h0
  rw [if_pos vector_one_mem] at h1
  have hd0 : dot w (vector (fun _ : Fin 8 => false))=0 := by simp [dot,vector,boolValue]
  rw [hd0] at h0
  norm_num at h0
  refine ⟨h0 ▸ c.ne_zero,?_⟩
  rw [h0,h1]
  have hsign (z : ZMod 2) : (-1:ℂ)^z.val=1 ∨ (-1:ℂ)^z.val= -1 := by
    fin_cases z
    · left; rfl
    · right
      change (-1:ℂ)^1= -1
      simp
  rcases hsign (dot w (vector (fun _ : Fin 8 => true))) with h | h
  · left; rw [h];simp
  · right; rw [h];simp

 theorem eigenvalues_equal_or_opposite (q : Signature ℂ 8) (hs : SupportRM (walsh q))
    (hd : PhysicalDeck q) (a b : ℂ) (hdet : det (mix a b)≠0) (p : Fin 8)
    (hdress : PhysicalDeck (onePort q (mix a b) p)) : a+b=a-b ∨ a+b= -(a-b) := by
  have hc := endpoint_character q hs hd
  have hd' := endpoint_character (onePort q (mix a b) p)
    (supportRM_onePort_mix q hs a b hdet p) hdress
  simp only [walsh_onePort_mix,Bool.false_eq_true,ite_false,ite_true] at hd'
  rcases hc.2 with hbase | hbase <;> rcases hd'.2 with hnew | hnew
  · rw [hbase] at hnew
    exact Or.inl ((mul_right_cancel₀ hc.1 hnew).symm)
  · rw [hbase] at hnew
    right
    apply (mul_right_cancel₀ hc.1)
    linear_combination hnew
  · rw [hbase] at hnew
    right
    apply (mul_right_cancel₀ hc.1)
    linear_combination -hnew
  · rw [hbase] at hnew
    left
    apply (mul_right_cancel₀ hc.1)
    linear_combination hnew

 theorem mix_scalar_I_or_X (a b : ℂ) (hdet : det (mix a b)≠0)
    (h : a+b=a-b ∨ a+b= -(a-b)) :
    (∃ c : ℂ,c≠0 ∧ mix a b=(fun x y => c*Signature.equality x y)) ∨
    (∃ c : ℂ,c≠0 ∧ mix a b=(fun x y => c*Signature.disequality x y)) := by
  rcases h with h | h
  · have hb : b=0 := by linear_combination h/2
    have ha : a≠0 := by intro hz;apply hdet;simp [det,mix,hz,hb]
    left
    refine ⟨a,ha,?_⟩
    funext x y
    simp [mix,hb,Signature.equality]
  · have ha : a=0 := by linear_combination h/2
    have hb : b≠0 := by intro hz;apply hdet;simp [det,mix,hz,ha]
    right
    refine ⟨b,hb,?_⟩
    funext x y
    by_cases hxy : x=y <;> simp [mix,ha,Signature.disequality,hxy]

/-- Every nonsingular transfer in the proper I/X algebra whose actual dressed
RM core remains in the physical matching deck is projectively I or X. -/
 theorem proper_safe_transfer_collapse (q : Signature ℂ 8) (hs : SupportRM (walsh q))
    (hd : PhysicalDeck q) (T : Mat) (hT : T∈Observability.ixSpan) (hdet : det T≠0)
    (p : Fin 8) (hdress : PhysicalDeck (onePort q T p)) :
    (∃ c : ℂ,c≠0 ∧ T=(fun x y => c*Signature.equality x y)) ∨
    (∃ c : ℂ,c≠0 ∧ T=(fun x y => c*Signature.disequality x y)) := by
  have hmix := proper_mix T hT
  rw [hmix] at hdet hdress ⊢
  exact mix_scalar_I_or_X _ _ hdet (eigenvalues_equal_or_opposite q hs hd _ _ hdet p hdress)

end
end Holant.ReedMuller.SafeCollapse
