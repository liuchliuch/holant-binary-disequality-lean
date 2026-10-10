import Holant.Certificates.RainbowOrbit.Deck
import Mathlib.LinearAlgebra.Projectivization.Collinear

namespace Holant.Certificates.RainbowOrbit
open Holant Holant.Certificates.MatchingProductBridge
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Ordinary projective collinearity supplies the two nonzero coefficients used
by the rank-one normalization; it is not a supplied normalization certificate. -/
theorem collinear_triple_iff (u v w : FourTensor) (hu : u≠0) (hv : v≠0) (hw : w≠0)
    (huv : ¬Proportional u v) (hwu : ¬Proportional w u) (hwv : ¬Proportional w v) :
    Projectivization.IsCollinear {Projectivization.mk ℂ u hu,Projectivization.mk ℂ v hv,
      Projectivization.mk ℂ w hw} ↔
    ∃ α β : ℂ, α≠0 ∧ β≠0 ∧ w=α • u+β • v := by
  have hne : Projectivization.mk ℂ u hu≠Projectivization.mk ℂ v hv :=
    fun h => huv ((proportional_point_iff u v hu hv).mpr h)
  have hli : LinearIndependent ℂ ![u,v] :=
    (Projectivization.independent_mk_iff_LinearIndependent hu hv).mp
      ((Projectivization.independent_pair_iff_ne _ _).mpr hne)
  have hdim : Module.finrank ℂ (Submodule.span ℂ ({u,v} : Set FourTensor))=2 := by
    rw [←Matrix.range_cons_cons_empty u v ![]]
    simpa using finrank_span_eq_card hli
  constructor
  · rintro ⟨M,hfin,hd,hm⟩
    letI := hfin
    have hum : u∈M.submodule := by
      have hh := hm (by simp : Projectivization.mk ℂ u hu∈
        ({Projectivization.mk ℂ u hu,Projectivization.mk ℂ v hv,Projectivization.mk ℂ w hw} : Set Point))
      exact (Projectivization.Subspace.mem_submodule_iff M hu).mpr hh
    have hvm : v∈M.submodule := by
      have hh := hm (by simp : Projectivization.mk ℂ v hv∈
        ({Projectivization.mk ℂ u hu,Projectivization.mk ℂ v hv,Projectivization.mk ℂ w hw} : Set Point))
      exact (Projectivization.Subspace.mem_submodule_iff M hv).mpr hh
    have hwm : w∈M.submodule := by
      have hh := hm (by simp : Projectivization.mk ℂ w hw∈
        ({Projectivization.mk ℂ u hu,Projectivization.mk ℂ v hv,Projectivization.mk ℂ w hw} : Set Point))
      exact (Projectivization.Subspace.mem_submodule_iff M hw).mpr hh
    have hle : Submodule.span ℂ ({u,v} : Set FourTensor)≤M.submodule := by
      apply Submodule.span_le.mpr
      intro x hx
      rcases hx with rfl|hx
      · exact hum
      · simpa using hx ▸ hvm
    have he := Submodule.eq_of_le_of_finrank_le hle (by simpa [hdim] using hd)
    rw [←he] at hwm
    obtain ⟨α,β,hline⟩ := Submodule.mem_span_pair.mp hwm
    refine ⟨α,β,?_,?_,hline.symm⟩
    · intro hz
      have hβ : β≠0 := by intro hz'; apply hw; simpa [hz,hz'] using hline.symm
      apply hwv
      exact ⟨β,hβ,by simpa [hz] using hline.symm⟩
    · intro hz
      have hα : α≠0 := by intro hz'; apply hw; simpa [hz,hz'] using hline.symm
      apply hwu
      exact ⟨α,hα,by simpa [hz] using hline.symm⟩
  · rintro ⟨α,β,hα,hβ,hline⟩
    refine ⟨(Submodule.span ℂ ({u,v} : Set FourTensor)).projectivization,
      ?_,?_,?_⟩
    · rw [Projectivization.Subspace.submodule.apply_symm_apply]
      exact Module.Finite.span_of_finite _ (Set.toFinite _)
    · rw [Projectivization.Subspace.submodule.apply_symm_apply]
      exact hdim.le
    · intro p hp
      rcases hp with rfl|rfl|hp
      · simp [Submodule.mem_span_of_mem]
      · simp [Submodule.mem_span_of_mem]
      · rcases hp with rfl
        apply (Submodule.mk_mem_projectivization_iff _ hw).mpr
        exact Submodule.mem_span_pair.mpr ⟨α,β,hline.symm⟩

end
end Holant.Certificates.RainbowOrbit
