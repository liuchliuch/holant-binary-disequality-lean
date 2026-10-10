import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeRankOneIncidence
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeMixedBlockRelabel
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeMixedBlockSource
import Holant.Proofs.Dichotomy.Closure.Eq4.GlobalCloseCompletionEq4FullSource

/-! Internally compile the exact arbitrary-coordinate two-point restriction
into actual retained ordinary rows and original-G programmes. Equal-degree
parity is proved from the selected words, not assumed as a compiler backend. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeRankOneSource
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.MainChain
namespace D
export OrdinaryNegativeMixedBlockData (Recipe EvenRecipe coefficient)
end D
namespace C
export OrdinaryNegativeRankOneCore (arity table recipe trace trace_value)
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
variable (j xLabel p₀ p₁ : Fin s)
variable (hx : (⟨b xLabel.val,H xLabel⟩ : AnySignature K)=
  ⟨2,fun x=>Signature.disequality (x 0) (x 1)⟩)
variable (h₀ : (⟨b p₀.val,H p₀⟩ : AnySignature K)=⟨1,OrdinaryNegativeRankOneCore.pin false⟩)
variable (h₁ : (⟨b p₁.val,H p₁⟩ : AnySignature K)=⟨1,OrdinaryNegativeRankOneCore.pin true⟩)
variable (x y : Fin (b j.val)→Bool)

def labels : Fin 4→Fin s := ![j,xLabel,p₀,p₁]

omit [Algebra ℚ K] in
include hx h₀ h₁ in
theorem literal (q : Fin 4) :
    (⟨b (labels j xLabel p₀ p₁ q).val,H (labels j xLabel p₀ p₁ q)⟩ : AnySignature K)=
      ⟨C.arity (b j.val) q.val,C.table (H j) q⟩ := by
  fin_cases q
  · rfl
  · exact hx
  · exact h₀
  · exact h₁

def blocks : D.Recipe (u:=1) (s:=s) (a:=fun _=>1+b j.val) (b:=b) :=
  R.exactRecipe (labels j xLabel p₀ p₁) (C.table (H j)) H
    (literal H j xLabel p₀ p₁ hx h₀ h₁) (C.recipe x y)

omit [Algebra ℚ K] in
theorem balanced (hd : Even (Dt.distance x y)) :
    D.EvenRecipe (blocks H j xLabel p₀ p₁ hx h₀ h₁ x y) :=
  R.even_recipe _ _ _ (I.even_recipe x y hd)

omit [Algebra ℚ K] in
theorem ports_exact (i : Fin 1) :
    OrdinaryNegativeMixedBlockData.ports (blocks H j xLabel p₀ p₁ hx h₀ h₁ x y) i=
      OrdinaryNegativeMixedBlockData.ports (C.recipe x y) i :=
  R.ports_eq _ _ _ i

omit [Algebra ℚ K] in
theorem boundary_count :
    (OrdinaryNegativeMixedBlockData.ports (blocks H j xLabel p₀ p₁ hx h₀ h₁ x y) 0).count (Sum.inr 0)=
      Dt.distance x y := by
  rw [ports_exact]
  exact I.external_count x y

omit [Algebra ℚ K] in
theorem away_even (q : Bool ⊕ Fin (1+b j.val)) (hq : q≠Sum.inr 0) :
    Even ((OrdinaryNegativeMixedBlockData.ports (blocks H j xLabel p₀ p₁ hx h₀ h₁ x y) 0).count q) := by
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
  M.trace H (b j.val) (blocks H j xLabel p₀ p₁ hx h₀ h₁ x y) 0

omit [Algebra ℚ K] in
theorem row_value (z : Fin 1→Bool) :
    row H j xLabel p₀ p₁ hx h₀ h₁ x y z=if z 0 then H j y else H j x := by
  change (∑v : Fin (b j.val)→Bool,D.coefficient H
    (blocks H j xLabel p₀ p₁ hx h₀ h₁ x y) 0 (Fin.addCases z v))=_
  simp only [blocks,R.coefficient_eq]
  exact C.trace_value (H j) x y z

variable (e : Fin s)
variable (he : (⟨b e.val,H e⟩ : AnySignature K)=⟨4,Holant.EightVertex.ProductAnchor.equalityFour⟩)

def source (hd : Even (Dt.distance x y)) :=
  M.privateControlled F H e p₀ p₁ he h₀ h₁ (b j.val)
    (blocks H j xLabel p₀ p₁ hx h₀ h₁ x y)
    (balanced H j xLabel p₀ p₁ hx h₀ h₁ x y hd)

omit [Algebra ℚ K] in
/-- Non-affineness is proved for the actually compiled unary resource. -/
theorem row_nonaffine (phi : K→+*AlgebraicComplex)
    (hleft : H j x≠0) (hright : H j y≠0)
    (bad : (phi (H j x))^4≠(phi (H j y))^4) :
    ¬Affine (fun z=>phi (row H j xLabel p₀ p₁ hx h₀ h₁ x y z)) := by
  intro ha
  apply bad
  have h := ha.fourth_power_eq (fun _=>false) (fun _=>true)
    (by simpa only [row_value,Bool.false_eq_true,ite_false] using (map_ne_zero phi).mpr hleft)
    (by simpa only [row_value,ite_true] using (map_ne_zero phi).mpr hright)
  simpa only [row_value,Bool.false_eq_true,ite_false,ite_true] using h
end Generic

section Original
namespace E
export GlobalCloseCompletionEq4FullSource (table arity xLabel pinLabel eq4Label
  x_literal pin_literal eq4_literal ordinarySource)
export GlobalCloseCompletionEq4CSPSource (field presentation)
end E
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (out : GlobalCloseCompletionEq4Graph.Output G P)
local instance : Algebra ℚ (E.field G P out) := (E.field G P out).algebra'
variable (j : Fin (GlobalCloseCompletionEq4FullSource.count G P))
variable (x y : Fin (E.arity G P out j.val)→Bool)

def originalBlocks := blocks (E.table G P out) j (E.xLabel G P) (E.pinLabel G P false)
  (E.pinLabel G P true) (E.x_literal G P out) (E.pin_literal G P out false)
  (E.pin_literal G P out true) x y

def originalRow := row (E.table G P out) j (E.xLabel G P) (E.pinLabel G P false)
  (E.pinLabel G P true) (E.x_literal G P out) (E.pin_literal G P out false)
  (E.pin_literal G P out true) x y

/-- All query substitutions and answer arithmetic terminate at unchanged G. -/
def originalSource (hd : Even (Dt.distance x y)) :=
  PhysicalProgramme.ofControlled (Programme.compose
    (source (E.presentation G P out) (E.table G P out) j (E.xLabel G P)
      (E.pinLabel G P false) (E.pinLabel G P true) (E.x_literal G P out)
      (E.pin_literal G P out false) (E.pin_literal G P out true) x y
      (E.eq4Label G P) (E.eq4_literal G P out) hd)
    (E.ordinarySource G P out))
end Original

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeRankOneSource
end
