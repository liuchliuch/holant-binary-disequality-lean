import Holant.ReedMuller.TwoChart.ContextKernelSum

/-! When the first actual chart has trivial character, every supported
localizer coefficient is one. The physical context can then use pure RM/I/X. -/
namespace Holant.ReedMuller.TwoChart
open Holant Holant.Tractable Holant.Tractable.AffinePhase Holant.Tractable.TwoTranslate
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.CharacterFlat Holant.ReedMuller.AffineRadon
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n m : ℕ}

theorem contextKernel_trivial_character (S J : BinaryCode n)
    (phi : S ≃ₗ[ZMod 2] BinaryVector m) (p : BinaryVector n) (chi : Character n)
    (hS : ∀s∈S,chi s=0) (hJ : ∀j∈J,chi j=0) :
    (fun z => (contextKernel S J phi p chi z:ℂ))=
      flatSignature 1 (joinVector p 0) (relationCode S J phi) := by
  funext z
  unfold contextKernel
  by_cases hz : vectorWord z-joinVector p 0∈relationCode S J phi
  · obtain ⟨⟨s,j⟩,he⟩ := hz
    have hL := congrArg leftVector he
    have hsub : leftVector (vectorWord z-joinVector p 0)=leftVector (vectorWord z)-p := by
      funext i
      simp [leftVector,joinVector]
    have heL : s.val+j.val=leftVector (vectorWord z)-p := by
      simpa only [relationMap,LinearMap.coe_mk,AddHom.coe_mk,left_join,hsub] using hL
    have hchi : chi (leftVector (vectorWord z)-p)=0 := by
      rw [←heL,map_add,hS _ s.property,hJ _ j.property,zero_add]
    have hz' : vectorWord z-joinVector p 0∈relationCode S J phi := ⟨⟨s,j⟩,he⟩
    rw [ite_eq_left hz',hchi]
    change ((fourthRootPhase (evenLift 0):AlgebraicComplex):ℂ)=
      if vectorWord z-joinVector p 0∈relationCode S J phi then (1:ℂ) else 0
    simp [hz']
  · rw [ite_eq_right hz]
    change (0:ℂ)=if vectorWord z-joinVector p 0∈relationCode S J phi then 1 else 0
    rw [ite_eq_right hz]

theorem contextKernel_flat (S J : BinaryCode n)
    (phi : S ≃ₗ[ZMod 2] BinaryVector m)
    (hphi : ∀s t : S,dot (phi s) (phi t)=dot s.val t.val)
    (hJ : ∀j∈J,∀k∈J,dot j k=0)
    (horth : ∀s∈S,∀j∈J,dot s j=0)
    (hdim : m+2*Module.finrank (ZMod 2) J=n)
    (p : BinaryVector n) (chi : Character n)
    (hchiS : ∀s∈S,chi s=0) (hchiJ : ∀j∈J,chi j=0) :
    Flat (fun z => (contextKernel S J phi p chi z:ℂ)) :=
  ⟨1,joinVector p 0,relationCode S J phi,
    relationCode_selfDual S J phi hphi hJ horth hdim,
    contextKernel_trivial_character S J phi p chi hchiS hchiJ⟩

variable {F : RadonAccess.RadonFrame n} {C₀ C₁ : Chart (n-2)}

theorem LocalizingData.context_flat (L : LocalizingData F C₀ C₁)
    (h₀ : C₀.character=0) : Flat (fun z => (L.context z:ℂ)) := by
  apply contextKernel_flat L.space L.isotropic L.coordinates L.isometry
    L.selfOrthogonal L.orthogonal L.halfDimension L.shift L.character L.character_space
  intro j hj
  rw [L.character_zero ⟨j,hj⟩]
  simp only [liftChart,LinearMap.comp_apply,h₀,LinearMap.zero_apply]

end
end Holant.ReedMuller.TwoChart
