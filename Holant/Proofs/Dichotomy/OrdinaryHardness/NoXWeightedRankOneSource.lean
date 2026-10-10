import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeRankOneIncidence
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeMixedBlockRelabel
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeMixedBlockSource
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXWeightedRankOneCore

/-! Exact original-label rank-one weighted-antidiagonal restriction.
The actual incidence parity is unchanged while all phase weights remain in the
source value. This file assumes no literal X row or classification backend. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXWeightedRankOneSource
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.MainChain
namespace D
export OrdinaryNegativeMixedBlockData (Recipe EvenRecipe coefficient)
end D
namespace C
export OrdinaryNegativeRankOneCore (arity recipe)
export NoXWeightedRankOneCore (table trace trace_value negativeCount)
end C
namespace I
export OrdinaryNegativeRankOneIncidence (even_recipe external_count private_count constant_count)
end I
namespace R
export OrdinaryNegativeMixedBlockRelabel (exactRecipe coefficient_eq even_recipe ports_eq)
end R
namespace M
export OrdinaryNegativeMixedBlockSource (trace privateControlled privateValue)
end M
namespace Dt
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseExtractionDistance (distance)
end Dt
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false

section Generic
variable {K : Type} [Field K] [Algebra ℚ K] {d s : ℕ} {b : ℕ→ℕ}
variable (F : FixedField K d) (H : (j : Fin s)→Signature K (b j.val))
variable (j antiLabel p₀ p₁ : Fin s)
variable (v w : K)
variable (ha_lit : (⟨b antiLabel.val,H antiLabel⟩ : AnySignature K)=
  ⟨2,NoXWeightedAntiSigned.anti v w⟩)
variable (h₀ : (⟨b p₀.val,H p₀⟩ : AnySignature K)=⟨1,OrdinaryNegativeRankOneCore.pin false⟩)
variable (h₁ : (⟨b p₁.val,H p₁⟩ : AnySignature K)=⟨1,OrdinaryNegativeRankOneCore.pin true⟩)
variable (x y : Fin (b j.val)→Bool)

def labels : Fin 4→Fin s := ![j,antiLabel,p₀,p₁]

omit [Algebra ℚ K] in
include ha_lit h₀ h₁ in
theorem literal (q : Fin 4) :
    (⟨b (labels j antiLabel p₀ p₁ q).val,H (labels j antiLabel p₀ p₁ q)⟩ : AnySignature K)=
      ⟨C.arity (b j.val) q.val,C.table (H j) v w q⟩ := by
  fin_cases q
  · rfl
  · exact ha_lit
  · exact h₀
  · exact h₁

def blocks : D.Recipe (u:=1) (s:=s) (a:=fun _=>1+b j.val) (b:=b) :=
  R.exactRecipe (labels j antiLabel p₀ p₁) (C.table (H j) v w) H
    (literal H j antiLabel p₀ p₁ v w ha_lit h₀ h₁) (C.recipe x y)

omit [Algebra ℚ K] in
theorem balanced (hd : Even (Dt.distance x y)) :
    D.EvenRecipe (blocks H j antiLabel p₀ p₁ v w ha_lit h₀ h₁ x y) :=
  R.even_recipe _ _ _ (I.even_recipe x y hd)

omit [Algebra ℚ K] in
theorem ports_exact (i : Fin 1) :
    OrdinaryNegativeMixedBlockData.ports (blocks H j antiLabel p₀ p₁ v w ha_lit h₀ h₁ x y) i=
      OrdinaryNegativeMixedBlockData.ports (C.recipe x y) i :=
  R.ports_eq _ _ _ i

omit [Algebra ℚ K] in
theorem boundary_count :
    (OrdinaryNegativeMixedBlockData.ports (blocks H j antiLabel p₀ p₁ v w ha_lit h₀ h₁ x y) 0).count (Sum.inr 0)=
      Dt.distance x y := by
  rw [ports_exact]
  exact I.external_count x y

omit [Algebra ℚ K] in
theorem away_even (q : Bool ⊕ Fin (1+b j.val)) (hq : q≠Sum.inr 0) :
    Even ((OrdinaryNegativeMixedBlockData.ports (blocks H j antiLabel p₀ p₁ v w ha_lit h₀ h₁ x y) 0).count q) := by
  rw [ports_exact]
  cases q with
  | inl v => rw [I.constant_count]; exact Even.mul_right (by decide : Even 2) _
  | inr v =>
      revert hq
      refine Fin.addCases ?_ ?_ v
      · intro z hz
        have he : z=0 := Fin.eq_zero z
        subst z
        exact False.elim (hz rfl)
      · intro z _
        rw [show Fin.natAdd 1 z=OrdinaryNegativeRankOneCore.privatePort z from rfl,I.private_count]
        decide

def row : Signature K 1 :=
  M.trace H (b j.val) (blocks H j antiLabel p₀ p₁ v w ha_lit h₀ h₁ x y) 0

omit [Algebra ℚ K] in
theorem row_value (z : Fin 1→Bool) :
    row H j antiLabel p₀ p₁ v w ha_lit h₀ h₁ x y z=
      (if z 0 then v else w)^C.negativeCount x y*(if z 0 then H j y else H j x) := by
  change (∑priv : Fin (b j.val)→Bool,D.coefficient H
    (blocks H j antiLabel p₀ p₁ v w ha_lit h₀ h₁ x y) 0 (Fin.addCases z priv))=_
  simp only [blocks,R.coefficient_eq]
  exact C.trace_value (H j) v w x y z

variable (e : Fin s)
variable (he : (⟨b e.val,H e⟩ : AnySignature K)=⟨4,Holant.EightVertex.ProductAnchor.equalityFour⟩)

def source (hd : Even (Dt.distance x y)) :=
  M.privateControlled F H e p₀ p₁ he h₀ h₁ (b j.val)
    (blocks H j antiLabel p₀ p₁ v w ha_lit h₀ h₁ x y)
    (balanced H j antiLabel p₀ p₁ v w ha_lit h₀ h₁ x y hd)

end Generic


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXWeightedRankOneSource
end
