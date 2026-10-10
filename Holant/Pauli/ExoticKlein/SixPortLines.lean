import Holant.Pauli.ExoticKlein.SixPortCards

/-! All forty-eight actual target lines, with explicit nonzero pivots. -/
namespace Holant.Pauli.ExoticKlein.SixPort
noncomputable section

 def directionEquiv : Fin 48 ≃ Direction :=
  (finProdFinEquiv (m := 3) (n := 16)).symm.trans
    (Equiv.prodCongr (Equiv.refl (Fin 3))
      ((finProdFinEquiv (m := 4) (n := 4)).symm.trans (Equiv.prodCongr labelEquiv labelEquiv)))

 def directionWord (d : Direction) : Fin 4 → Bool :=
  if d.1 = 0 then ![false,decide (d.2.1 = xLabel),false,decide (d.2.2 = xLabel)]
  else if d.1 = 1 then ![false,false,decide (d.2.1 = xLabel),decide (d.2.2 = xLabel)]
  else ![false,false,decide (d.2.2 = xLabel),decide (d.2.1 = xLabel)]

 theorem gaussianDirection_pivot_nonzero (d : Direction) : gaussianDirection d (directionWord d) ≠ 0 := by
  revert d
  decide +kernel

 def lineVector (j : Fin 48) : Fin 16 → LinearCertificate.Q :=
  fun word => gaussianDirection (directionEquiv j) ((wordEquiv 4).symm word)

 def linePivot (j : Fin 48) : Fin 16 := wordEquiv 4 (directionWord (directionEquiv j))

 theorem linePivot_nonzero (j : Fin 48) : lineVector j (linePivot j) ≠ 0 := by
  simp only [lineVector,linePivot,Equiv.symm_apply_apply]
  exact gaussianDirection_pivot_nonzero _

 theorem lineVector_semantics (j : Fin 48) (word : Fin 16) :
    Algebraic.gaussianToComplex (lineVector j word) =
      directionTensor (directionEquiv j) ((wordEquiv 4).symm word) := map_gaussianDirection _ _

/-- A safe ordered four-port tensor is a scalar on one of the literal lines;
zero is included without a liveness test on its target scalar. -/
 def OnDirection (h : Signature ℂ 4) : Prop :=
  ∃ d : Direction, ∃ s : ℂ, h = fun x => s*directionTensor d x

 theorem onDirection_iff_lines (h : Signature ℂ 4) : OnDirection h ↔
    ∃ j : Fin 48, ∃ s : ℂ, ∀ word : Fin 16,
      h ((wordEquiv 4).symm word) = s*Algebraic.gaussianToComplex (lineVector j word) := by
  constructor
  · rintro ⟨d,s,rfl⟩
    refine ⟨directionEquiv.symm d,s,?_⟩
    intro word
    rw [lineVector_semantics,Equiv.apply_symm_apply]
  · rintro ⟨j,s,hs⟩
    refine ⟨directionEquiv j,s,?_⟩
    funext x
    have hx := hs (wordEquiv 4 x)
    simpa only [lineVector_semantics,Equiv.symm_apply_apply] using hx

 theorem zero_onDirection : OnDirection (0 : Signature ℂ 4) :=
  ⟨baseDirection,0,by funext x; simp⟩

end
end Holant.Pauli.ExoticKlein.SixPort
