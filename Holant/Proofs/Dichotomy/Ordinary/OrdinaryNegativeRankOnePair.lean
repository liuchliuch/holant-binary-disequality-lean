import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeRankOneSource
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeMixedBlockOverlay

/-! Overlay two actual two-point restrictions with separate private variables.
The selected rows may have different arities. Only the sum of their two
Hamming distances must be even: neither boundary must be even separately.
All original coefficients are retained, without squaring either resource. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeRankOnePair
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.MainChain
namespace D
export OrdinaryNegativeMixedBlockData (Recipe EvenRecipe)
end D
namespace R
export OrdinaryNegativeRankOneSource (blocks row row_value boundary_count away_even)
end R
namespace O
export OrdinaryNegativeMixedBlockOverlay (recipe even_recipe trace_eq)
end O
namespace M
export OrdinaryNegativeMixedBlockSource (trace privateControlled)
end M
namespace Dt
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseExtractionDistance (distance)
end Dt
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false

variable {K : Type} [Field K] {s : ℕ} {b : ℕ→ℕ}
variable (H : (j : Fin s)→Signature K (b j.val))
variable (j q xLabel p₀ p₁ : Fin s)
variable (hx : (⟨b xLabel.val,H xLabel⟩ : AnySignature K)=
  ⟨2,fun x=>Signature.disequality (x 0) (x 1)⟩)
variable (h₀ : (⟨b p₀.val,H p₀⟩ : AnySignature K)=⟨1,OrdinaryNegativeRankOneCore.pin false⟩)
variable (h₁ : (⟨b p₁.val,H p₁⟩ : AnySignature K)=⟨1,OrdinaryNegativeRankOneCore.pin true⟩)
variable (x₁ y₁ : Fin (b j.val)→Bool) (x₂ y₂ : Fin (b q.val)→Bool)

def blocks : D.Recipe (u:=1) (s:=s) (a:=fun _=>1+(b j.val+b q.val)) (b:=b) :=
  O.recipe (R.blocks H j xLabel p₀ p₁ hx h₀ h₁ x₁ y₁)
    (R.blocks H q xLabel p₀ p₁ hx h₀ h₁ x₂ y₂)

/-- Each odd boundary can be balanced by the other restriction's boundary. -/
theorem balanced (hd : Even (Dt.distance x₁ y₁+Dt.distance x₂ y₂)) :
    D.EvenRecipe (blocks H j q xLabel p₀ p₁ hx h₀ h₁ x₁ y₁ x₂ y₂) := by
  apply O.even_recipe
  · exact R.away_even H j xLabel p₀ p₁ hx h₀ h₁ x₁ y₁
  · exact R.away_even H q xLabel p₀ p₁ hx h₀ h₁ x₂ y₂
  · rw [R.boundary_count,R.boundary_count]
    exact hd

def row : Signature K 1 :=
  M.trace H (b j.val+b q.val) (blocks H j q xLabel p₀ p₁ hx h₀ h₁ x₁ y₁ x₂ y₂) 0

/-- The surviving endpoints are the two original coefficient products. -/
theorem row_value (z : Fin 1→Bool) :
    row H j q xLabel p₀ p₁ hx h₀ h₁ x₁ y₁ x₂ y₂ z=
      if z 0 then H j y₁*H q y₂ else H j x₁*H q x₂ := by
  unfold row blocks
  rw [O.trace_eq]
  change R.row H j xLabel p₀ p₁ hx h₀ h₁ x₁ y₁ z *
    R.row H q xLabel p₀ p₁ hx h₀ h₁ x₂ y₂ z=_
  rw [R.row_value,R.row_value]
  cases z 0 <;> rfl

/-- A fourth-power conflict in the actual endpoint products is non-affine. -/
theorem row_nonaffine (phi : K→+*AlgebraicComplex)
    (hleft : H j x₁*H q x₂≠0) (hright : H j y₁*H q y₂≠0)
    (bad : (phi (H j x₁*H q x₂))^4≠(phi (H j y₁*H q y₂))^4) :
    ¬Affine (fun z=>phi (row H j q xLabel p₀ p₁ hx h₀ h₁ x₁ y₁ x₂ y₂ z)) := by
  intro ha
  apply bad
  have h := ha.fourth_power_eq (fun _=>false) (fun _=>true)
    (by simpa only [row_value,Bool.false_eq_true,ite_false] using (map_ne_zero phi).mpr hleft)
    (by simpa only [row_value,ite_true] using (map_ne_zero phi).mpr hright)
  simpa only [row_value,Bool.false_eq_true,ite_false,ite_true] using h

theorem row_supported (phi : K→+*AlgebraicComplex)
    (hleft : H j x₁*H q x₂≠0) (hright : H j y₁*H q y₂≠0) (z : Fin 1→Bool) :
    phi (row H j q xLabel p₀ p₁ hx h₀ h₁ x₁ y₁ x₂ y₂ z)≠0 := by
  rw [row_value]
  cases z 0
  · exact (map_ne_zero phi).mpr hleft
  · exact (map_ne_zero phi).mpr hright

theorem row_closed (phi : K→+*AlgebraicComplex)
    (hleft : H j x₁*H q x₂≠0) (hright : H j y₁*H q y₂≠0) :
    Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEONegativeClosedSupport.Closed
      (fun z=>phi (row H j q xLabel p₀ p₁ hx h₀ h₁ x₁ y₁ x₂ y₂ z)) := by
  intro u v w _ _ _
  exact row_supported H j q xLabel p₀ p₁ hx h₀ h₁ x₁ y₁ x₂ y₂ phi hleft hright _

variable [Algebra ℚ K] {d : ℕ} (F : FixedField K d)
variable (e : Fin s)
variable (he : (⟨b e.val,H e⟩ : AnySignature K)=⟨4,Holant.EightVertex.ProductAnchor.equalityFour⟩)

def source (hd : Even (Dt.distance x₁ y₁+Dt.distance x₂ y₂)) :=
  M.privateControlled F H e p₀ p₁ he h₀ h₁ (b j.val+b q.val)
    (blocks H j q xLabel p₀ p₁ hx h₀ h₁ x₁ y₁ x₂ y₂)
    (balanced H j q xLabel p₀ p₁ hx h₀ h₁ x₁ y₁ x₂ y₂ hd)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeRankOnePair
end
