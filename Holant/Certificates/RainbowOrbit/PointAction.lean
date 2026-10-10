import Holant.Certificates.RainbowOrbit.Lines

namespace Holant.Certificates.RainbowOrbit
open Holant Holant.Certificates.MatchingProductBridge
noncomputable section
set_option backward.isDefEq.respectTransparency false

def actionLinear (L : Legs) : FourTensor →ₗ[ℂ] FourTensor where
  toFun := act L
  map_add' := act_add L
  map_smul' := act_smul L

theorem actionLinear_injective (L : Legs) (hL : ∀j,(L j).det≠0) :
    Function.Injective (actionLinear L) := by
  intro F H he
  have hh := congrArg (act (fun j => (L j)⁻¹)) he
  simpa only [actionLinear,LinearMap.coe_mk,AddHom.coe_mk,act_inverse L hL] using hh

def pointAction (L : Legs) (hL : ∀j,(L j).det≠0) : Point→Point :=
  Projectivization.map (actionLinear L) (actionLinear_injective L hL)

@[simp] theorem pointAction_mk (L : Legs) (hL : ∀j,(L j).det≠0) (F : FourTensor) (hF : F≠0) :
    pointAction L hL (Projectivization.mk ℂ F hF)=
      Projectivization.mk ℂ (act L F) (act_nonzero L hL hF) := rfl

theorem pointAction_injective (L : Legs) (hL : ∀j,(L j).det≠0) :
    Function.Injective (pointAction L hL) := Projectivization.map_injective _ _

theorem inverseLegs_det (L : Legs) (hL : ∀j,(L j).det≠0) :
    ∀j,((L j)⁻¹).det≠0 := by intro j; simpa [Matrix.det_nonsing_inv] using hL j

theorem pointAction_inverse (L : Legs) (hL : ∀j,(L j).det≠0) (p : Point) :
    pointAction (fun j => (L j)⁻¹) (inverseLegs_det L hL) (pointAction L hL p)=p := by
  induction p using Projectivization.ind with | h F hF =>
  simp only [pointAction_mk]
  congr 1
  exact act_inverse L hL F

theorem pointAction_collinear (L : Legs) (hL : ∀j,(L j).det≠0) (S : Set Point)
    (hS : Projectivization.IsCollinear S) :
    Projectivization.IsCollinear (pointAction L hL '' S) := by
  obtain ⟨M,hfin,hd,hm⟩ := hS
  letI := hfin
  let N := M.submodule.map (actionLinear L)
  refine ⟨N.projectivization,?_,?_,?_⟩
  · rw [Projectivization.Subspace.submodule.apply_symm_apply]
    exact Module.Finite.map _ _
  · rw [Projectivization.Subspace.submodule.apply_symm_apply]
    exact (Submodule.finrank_map_le _ _).trans hd
  · rintro p ⟨q,hq,rfl⟩
    induction q using Projectivization.ind with | h F hF =>
    rw [pointAction_mk]
    change act L F∈N
    exact Submodule.mem_map.mpr ⟨F,(Projectivization.Subspace.mem_submodule_iff M hF).mpr (hm hq),rfl⟩

theorem pointAction_collinear_iff (L : Legs) (hL : ∀j,(L j).det≠0) (S : Set Point) :
    Projectivization.IsCollinear (pointAction L hL '' S) ↔ Projectivization.IsCollinear S := by
  constructor
  · intro h
    have hh := pointAction_collinear (fun j => (L j)⁻¹) (inverseLegs_det L hL) _ h
    have he : pointAction (fun j => (L j)⁻¹) (inverseLegs_det L hL) '' (pointAction L hL '' S)=S := by
      rw [←Set.image_comp]
      simp only [Function.comp_def,pointAction_inverse]
      ext p
      simp
    rwa [he] at hh
  · exact pointAction_collinear L hL S

end
end Holant.Certificates.RainbowOrbit
