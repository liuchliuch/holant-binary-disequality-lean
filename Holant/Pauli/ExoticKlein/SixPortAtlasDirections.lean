import Holant.Pauli.ExoticKlein.SixPortAtlasModel
import Holant.Pauli.ExoticKlein.SixPortMatchingLines

/-! Faithful projective direction count for A.12. The48actual quaternary
matching directions are complete, nonzero and pairwise projectively distinct. -/
namespace Holant.Pauli.ExoticKlein.SixPort.Atlas
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
set_option Elab.async false

theorem integer_directions_distinct :
    ∀ i j : Fin 48,
      (∀ w, integerLine i w*integerLine j (linePivot i) =
        integerLine j w*integerLine i (linePivot i)) → i = j := by
  decide +kernel

theorem eval_integerLine (i : Fin 48) (w : Fin 16) :
    evalInteger (integerLine i w) = directionTensor (directionEquiv i) ((wordEquiv 4).symm w) := by
  change Algebraic.gaussianToComplex (integerToGaussian (integerLine i w)) = _
  rw [integerLine_correct,lineVector_semantics]

theorem directions_projectively_distinct (i j : Fin 48) (c : ℂ)
    (he : directionTensor (directionEquiv i) = fun x => c*directionTensor (directionEquiv j) x) : i = j := by
  apply integer_directions_distinct i j
  intro w
  apply evalInteger_injective
  simp only [map_mul,eval_integerLine,he]
  ring

theorem direction_nonzero (i : Fin 48) : directionTensor (directionEquiv i) ≠ 0 := by
  intro hz
  have he := congrFun hz ((wordEquiv 4).symm (linePivot i))
  rw [←lineVector_semantics] at he
  have hh : lineVector i (linePivot i) = 0 := Algebraic.gaussianToComplex_injective
    (he.trans (map_zero _).symm)
  exact linePivot_nonzero i hh

theorem directions_complete (h : Signature ℂ 4) (hn : h ≠ 0)
    (hh : h = 0 ∨ ∃ M : Matching (Fin 4) 2, ∃ labels : Fin 2 → Label, ∃ c : ℂ,
      c ≠ 0 ∧ h = fun x => c*M.tensor labels x) :
    ∃ i : Fin 48, ∃ c : ℂ, c ≠ 0 ∧ h = fun x => c*directionTensor (directionEquiv i) x := by
  obtain ⟨d,c,he⟩ := (onDirection_iff_matching h).mpr hh
  have hc : c ≠ 0 := by
    intro hz
    apply hn
    rw [he,hz]
    funext x
    simp
  exact ⟨directionEquiv.symm d,c,hc,by simpa only [Equiv.apply_symm_apply] using he⟩

end
end Holant.Pauli.ExoticKlein.SixPort.Atlas
