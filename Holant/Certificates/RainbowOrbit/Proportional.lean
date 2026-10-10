import Holant.Certificates.RainbowOrbit.Action
import Mathlib.LinearAlgebra.Projectivization.Basic

namespace Holant.Certificates.RainbowOrbit
open Holant Holant.Certificates.MatchingProductBridge
noncomputable section
set_option backward.isDefEq.respectTransparency false

def Proportional {V : Type*} [AddCommGroup V] [Module ℂ V] (u v : V) : Prop :=
  ∃ c : ℂ, c≠0 ∧ u=c • v

theorem Proportional.refl {V : Type*} [AddCommGroup V] [Module ℂ V] (u : V) : Proportional u u :=
  ⟨1,one_ne_zero,by simp⟩

theorem Proportional.symm {V : Type*} [AddCommGroup V] [Module ℂ V] {u v : V}
    (h : Proportional u v) : Proportional v u := by
  obtain ⟨c,hc,rfl⟩ := h
  exact ⟨c⁻¹,inv_ne_zero hc,by simp [smul_smul,hc]⟩

theorem Proportional.trans {V : Type*} [AddCommGroup V] [Module ℂ V] {u v w : V}
    (huv : Proportional u v) (hvw : Proportional v w) : Proportional u w := by
  obtain ⟨c,hc,rfl⟩ := huv
  obtain ⟨d,hd,rfl⟩ := hvw
  exact ⟨c*d,mul_ne_zero hc hd,by rw [smul_smul]⟩

theorem proportional_point_iff {V : Type*} [AddCommGroup V] [Module ℂ V]
    (u v : V) (hu : u≠0) (hv : v≠0) :
    Proportional u v ↔ Projectivization.mk ℂ u hu=Projectivization.mk ℂ v hv := by
  rw [Projectivization.mk_eq_mk_iff']
  constructor
  · rintro ⟨c,hc,he⟩
    exact ⟨c,he.symm⟩
  · rintro ⟨c,he⟩
    refine ⟨c,?_,he.symm⟩
    intro hc
    exact hu (by simpa [hc] using he.symm)

theorem Proportional.act {F H : FourTensor} (h : Proportional F H) (L : Legs) :
    Proportional (act L F) (act L H) := by
  obtain ⟨c,hc,rfl⟩ := h
  exact ⟨c,hc,act_smul L c H⟩

theorem proportional_act_iff (L : Legs) (hL : ∀ j, Matrix.det (L j)≠0) (F H : FourTensor) :
    Proportional (act L F) (act L H) ↔ Proportional F H := by
  constructor
  · intro hp
    have hh := hp.act (fun j => (L j)⁻¹)
    simpa only [act_inverse L hL] using hh
  · intro hp
    exact hp.act L

theorem matching_nonzero (r : Fin 3) (U V : BinaryMatrix) (hU : U.det≠0) (hV : V.det≠0) :
    matchingTensor r U V≠0 := by
  intro hz
  have hr := matching_flattening_rank r r U V hU hV
  rw [hz,flatten_zero] at hr
  simp at hr

theorem proportional_matching_labels (r s : Fin 3) (U V U' V' : BinaryMatrix)
    (hU : U.det≠0) (hV : V.det≠0) (hU' : U'.det≠0) (hV' : V'.det≠0)
    (h : Proportional (matchingTensor r U V) (matchingTensor s U' V')) : r=s := by
  obtain ⟨c,hc,he⟩ := h
  have hh := congrArg (fun F => (flatten r F).rank) he
  rw [flatten_smul,Matrix.rank_smul_of_mem_nonZeroDivisors _ (mem_nonZeroDivisors_of_ne_zero hc),
    matching_flattening_rank r r U V hU hV,matching_flattening_rank r s U' V' hU' hV'] at hh
  by_contra hrs
  simp [hrs] at hh

end
end Holant.Certificates.RainbowOrbit
