import Holant.ReedMuller.TwoChart.ProjectedData

/-! Literal noncancelling fiber witnesses for the two localization branches.
The missing fourth point follows from an original separating inner product. -/
namespace Holant.ReedMuller.TwoChart
open Holant Holant.Tractable Holant.Tractable.AffinePhase Holant.Tractable.TwoTranslate
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.CharacterFlat Holant.ReedMuller.AffinePatching
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

 theorem signedChartSum_shift_add_nonzero (C : Chart n) (J : BinaryCode n) (chi : Character n)
    (hchi : ∀ j : J,chi j.val=C.character j.val)
    (s : BinaryVector n) (hs : s∈C.direction) : signedChartSum C J chi (C.shift+s)≠0 := by
  apply (signedChartSum_nonzero_iff C J chi hchi _).mpr
  exact ⟨0,by simpa using hs⟩

 theorem signedChartSum_separating_zero (C : Chart n) (J : BinaryCode n) (chi : Character n)
    (hchi : ∀ j : J,chi j.val=C.character j.val)
    (s t : BinaryVector n) (ht : t∈C.direction) (hst : dot s t=1)
    (hJt : ∀ j : J,dot j.val t=0) : signedChartSum C J chi (C.shift+s)=0 := by
  by_contra hn
  obtain ⟨j,hj⟩ := (signedChartSum_nonzero_iff C J chi hchi _).mp hn
  have hj' : s+j.val∈C.direction := by
    have he : C.shift+s+j.val-C.shift=s+j.val := by abel
    rwa [he] at hj
  have H := (C.selfDual _).mp hj' t ht
  rw [dot_add_left,hst,hJt,add_zero] at H
  exact one_ne_zero H

 theorem nonaffine_of_missing_parallelogram (f : Signature AlgebraicComplex n)
    (a s b : BinaryVector n)
    (h₀ : f (wordVector a)≠0) (h₁ : f (wordVector (a+s))≠0)
    (h₂ : f (wordVector b)≠0) (h₃ : f (wordVector (b+s))=0) : ¬Affine f := by
  intro hf
  have H := affine_support_ternary f hf (wordVector a) (wordVector (a+s)) (wordVector b) h₀ h₁ h₂
  have he : xor (xor (wordVector a) (wordVector (a+s))) (wordVector b)=wordVector (b+s) := by
    apply vector_injective
    simp only [vector_xor,vector_word]
    have ha : a+a=0 := RadonAccess.binary_add_self _
    calc
      a+(a+s)+b=(a+a)+(b+s) := by abel
      _=b+s := by rw [ha,zero_add]
  rw [he,h₃] at H
  exact H rfl

 theorem nonaffine_of_forbidden_ratio (f : Signature AlgebraicComplex n)
    (a b : Word n) (ha : f a≠0) (hb : f b≠0)
    (hr : (f b/f a)^4≠1) : ¬Affine f := by
  intro hf
  have H := hf.fourth_power_eq b a hb ha
  apply hr
  rw [div_pow,H,div_self (pow_ne_zero 4 ha)]

end
end Holant.ReedMuller.TwoChart
