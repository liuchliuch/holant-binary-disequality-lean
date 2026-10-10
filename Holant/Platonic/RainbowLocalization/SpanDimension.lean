import Holant.Platonic.RainbowLocalization.CommonComplement
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-! The actual two-dimensional span after compatible factor rescaling. -/
namespace Holant.Platonic.RainbowLocalization
noncomputable section
open Holant.Certificates.RainbowOrbit
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

 theorem nonproportional_span_pair_finrank (u v : V) (hu : u≠0) (hv : v≠0)
    (h : ¬Proportional u v) : Module.finrank ℂ (Submodule.span ℂ ({u,v} : Set V))=2 := by
  have hi : LinearIndependent ℂ ![u,v] := by
    apply linearIndependent_fin2.mpr
    refine ⟨hv,?_⟩
    intro c hc
    apply h
    refine ⟨c,?_,hc.symm⟩
    intro hz
    exact hu (by simpa [hz] using hc.symm)
  have hrange : Set.range (![u,v] : Fin 2→V)=({u,v} : Set V) := by
    ext z
    constructor
    · rintro ⟨i,rfl⟩
      fin_cases i <;> simp
    · rintro (rfl|rfl)
      · exact ⟨0,rfl⟩
      · exact ⟨1,rfl⟩
  have hh := finrank_span_eq_card hi
  rw [hrange] at hh
  simpa using hh

 theorem span_triple_eq_pair (u v w : V) (a b : ℂ) (hw : w=a • u+b • v) :
    Submodule.span ℂ ({u,v,w} : Set V)=Submodule.span ℂ ({u,v} : Set V) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro x hx
    rcases hx with rfl|rfl|rfl
    · exact Submodule.subset_span (by simp)
    · exact Submodule.subset_span (by simp)
    · rw [hw]
      exact Submodule.add_mem _
        (Submodule.smul_mem _ a (Submodule.subset_span (by simp)))
        (Submodule.smul_mem _ b (Submodule.subset_span (by simp)))
  · exact Submodule.span_mono (by intro x hx;rcases hx with rfl|rfl <;> simp)

 theorem nonproportional_span_triple_finrank (u v w : V) (hu : u≠0) (hv : v≠0)
    (h : ¬Proportional u v) (a b : ℂ) (hw : w=a • u+b • v) :
    Module.finrank ℂ (Submodule.span ℂ ({u,v,w} : Set V))=2 := by
  rw [span_triple_eq_pair u v w a b hw]
  exact nonproportional_span_pair_finrank u v hu hv h

end
end Holant.Platonic.RainbowLocalization
