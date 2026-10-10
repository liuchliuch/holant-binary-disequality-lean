import Holant.ReedMuller.CharacterFlat.FactorSlice

/-! Closure under genuine nonzero tensor factors, without assuming a support
code or a character for either factor. -/
namespace Holant.ReedMuller.CharacterFlat
open Holant Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {m n : ℕ}

theorem nonzeroFlat_factors (f : Signature ℂ m) (g : Signature ℂ n)
    (h : NonzeroFlat (Signature.tensor f g)) : NonzeroFlat f ∧ NonzeroFlat g := by
  obtain ⟨c,a,D,ell,hD,he⟩ := h
  let F : BinaryVector m → ℂ := fun x => f (wordVector x)
  let G : BinaryVector n → ℂ := fun y => g (wordVector y)
  have hvalues : ∀ x y,F x*G y=value c a D ell (joinVector x y) := by
    intro x y
    have H := congrFun he (wordVector (joinVector x y))
    change f (fun i => wordVector (joinVector x y) (Fin.castAdd n i))*
      g (fun i => wordVector (joinVector x y) (Fin.natAdd m i))=
      value c a D ell (vectorWord (wordVector (joinVector x y))) at H
    rw [vector_word] at H
    change (f (fun i => boolEquiv.symm (x i)))*(g (fun i => boolEquiv.symm (y i)))=_
    simpa only [wordVector,joinVector,Fin.addCases_left,Fin.addCases_right] using H
  have hs := factor_code_splits F G c c.ne_zero a D ell hvalues
  obtain ⟨c₁,c₂,hc₁,hc₂,hf,hg⟩ := factor_values F G c c.ne_zero a D ell hvalues
  constructor
  · refine ⟨Units.mk0 c₁ hc₁,leftVector a,leftCode D,ell.comp leftEmbedding,
      leftCode_selfDual D hD hs,?_⟩
    funext x
    have H := congrFun hf (vectorWord x)
    simpa only [F,word_vector,signature,Units.val_mk0] using H
  · refine ⟨Units.mk0 c₂ hc₂,rightVector a,rightCode D,ell.comp rightEmbedding,
      rightCode_selfDual D hD hs,?_⟩
    funext x
    have H := congrFun hg (vectorWord x)
    simpa only [G,word_vector,signature,Units.val_mk0] using H

/-- The source's nonzero factor clause, with actual tensor equality. -/
theorem CFlat.factors (f : Signature ℂ m) (g : Signature ℂ n)
    (h : CFlat (Signature.tensor f g)) (hn : Signature.tensor f g≠0) :
    NonzeroFlat f ∧ NonzeroFlat g :=
  nonzeroFlat_factors f g (h.resolve_left hn)

end
end Holant.ReedMuller.CharacterFlat
