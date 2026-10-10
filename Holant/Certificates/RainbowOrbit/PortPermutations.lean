import Holant.Certificates.RainbowOrbit.PointAction
import Holant.Certificates.RainbowOrbit.NoRainbow

namespace Holant.Certificates.RainbowOrbit
open Holant Holant.Certificates.MatchingProductBridge
noncomputable section
set_option backward.isDefEq.respectTransparency false

def adjacent (j : Fin 3) : Equiv.Perm (Fin 4) := Equiv.swap j.castSucc j.succ

def adjacentLabels (j : Fin 3) : Equiv.Perm (Fin 3) :=
  if j=1 then Equiv.swap 0 1 else Equiv.swap 1 2

theorem adjacent_matching (G : BinaryMatrix→Prop)
    (htranspose : ∀{U : BinaryMatrix},G U→G U.transpose)
    (j r : Fin 3) (U V : BinaryMatrix) (hU : G U) (hV : G V) :
    ∃S T : BinaryMatrix,G S ∧ G T ∧
      Tensor.reindex (adjacent j) (matchingTensor r U V)=matchingTensor (adjacentLabels j r) S T := by
  fin_cases j <;> fin_cases r
  · refine ⟨U.transpose,V,htranspose hU,hV,?_⟩
    funext x
    simp [adjacent,adjacentLabels,Tensor.reindex,matchingTensor,P0,P1,P2,Equiv.swap_apply_def]
  · refine ⟨V,U,hV,hU,?_⟩
    funext x
    simp [adjacent,adjacentLabels,Tensor.reindex,matchingTensor,P0,P1,P2,Equiv.swap_apply_def,mul_comm]
  · refine ⟨V,U,hV,hU,?_⟩
    funext x
    simp [adjacent,adjacentLabels,Tensor.reindex,matchingTensor,P0,P1,P2,Equiv.swap_apply_def,mul_comm]
  · refine ⟨U,V,hU,hV,?_⟩
    funext x
    simp [adjacent,adjacentLabels,Tensor.reindex,matchingTensor,P0,P1,P2,Equiv.swap_apply_def]
  · refine ⟨U,V,hU,hV,?_⟩
    funext x
    simp [adjacent,adjacentLabels,Tensor.reindex,matchingTensor,P0,P1,P2,Equiv.swap_apply_def]
  · refine ⟨U,V.transpose,hU,htranspose hV,?_⟩
    funext x
    simp [adjacent,adjacentLabels,Tensor.reindex,matchingTensor,P0,P1,P2,Equiv.swap_apply_def]
  · refine ⟨U,V.transpose,hU,htranspose hV,?_⟩
    funext x
    simp [adjacent,adjacentLabels,Tensor.reindex,matchingTensor,P0,P1,P2,Equiv.swap_apply_def]
  · refine ⟨U,V,hU,hV,?_⟩
    funext x
    simp [adjacent,adjacentLabels,Tensor.reindex,matchingTensor,P0,P1,P2,Equiv.swap_apply_def]
  · refine ⟨U,V,hU,hV,?_⟩
    funext x
    simp [adjacent,adjacentLabels,Tensor.reindex,matchingTensor,P0,P1,P2,Equiv.swap_apply_def]

def portLinear (e : Equiv.Perm (Fin 4)) : FourTensor→ₗ[ℂ] FourTensor where
  toFun := Tensor.reindex e
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem portLinear_injective (e : Equiv.Perm (Fin 4)) : Function.Injective (portLinear e) := by
  intro F H he
  have hh := congrArg (Tensor.reindex e.symm) he
  simpa only [portLinear,LinearMap.coe_mk,AddHom.coe_mk,Tensor.reindex_symm] using hh

def portPoint (e : Equiv.Perm (Fin 4)) : Point→Point :=
  Projectivization.map (portLinear e) (portLinear_injective e)

theorem portPoint_injective (e : Equiv.Perm (Fin 4)) : Function.Injective (portPoint e) :=
  Projectivization.map_injective _ _

theorem linearMap_collinear (L : FourTensor→ₗ[ℂ] FourTensor) (hL : Function.Injective L) (S : Set Point)
    (hS : Projectivization.IsCollinear S) :
    Projectivization.IsCollinear (Projectivization.map L hL '' S) := by
  obtain ⟨M,hfin,hd,hm⟩ := hS
  letI := hfin
  let N := M.submodule.map L
  refine ⟨N.projectivization,?_,?_,?_⟩
  · rw [Projectivization.Subspace.submodule.apply_symm_apply]
    exact Module.Finite.map _ _
  · rw [Projectivization.Subspace.submodule.apply_symm_apply]
    exact (Submodule.finrank_map_le _ _).trans hd
  · rintro p ⟨q,hq,rfl⟩
    induction q using Projectivization.ind with | h F hF =>
    rw [Projectivization.map_mk]
    change L F∈N
    exact Submodule.mem_map.mpr ⟨F,(Projectivization.Subspace.mem_submodule_iff M hF).mpr (hm hq),rfl⟩

theorem portPoint_collinear (e : Equiv.Perm (Fin 4)) (S : Set Point)
    (hS : Projectivization.IsCollinear S) : Projectivization.IsCollinear (portPoint e '' S) :=
  linearMap_collinear (portLinear e) (portLinear_injective e) S hS

end
end Holant.Certificates.RainbowOrbit
