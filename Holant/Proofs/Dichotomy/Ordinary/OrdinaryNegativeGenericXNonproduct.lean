import Holant.Proofs.Dichotomy.General.GenericLiteralXSource
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeNonproductBundleSource
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeAffineSupportClosure

/-! The actual literal-X ordinary obstruction internally supplies its own
non-Product even resource. Closed support is inherited from the original row;
it is not supplied separately for the selected at-most-sixteen-row block. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeGenericXNonproduct
open Computability Holant Holant.Tractable Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace E
export GenericLiteralXSource (count arity table family eq4Label pinLabel
  eq4_literal pin_literal ordinarySource)
export GenericLiteralXSource (field presentation)
end E
namespace B
export OrdinaryNegativeNonproductBundleChoice (Choice choose)
end B
namespace R
export OrdinaryNegativeNonproductBundleSource (recipe even_recipe coefficient_eq controlled)
end R
namespace D
export OrdinaryNegativeMixedBlockData (Recipe EvenRecipe coefficient)
export OrdinaryNegativeMixedBlockSource (trace)
end D
namespace C
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEONegativeClosedSupport (Closed)
export OrdinaryNegativeAffineSupportClosure (nonproduct_choice_closed)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (src : GenericLiteralXSource.Data G)
local instance : Algebra ℚ (E.field G src) := (E.field G src).algebra'
variable (negative : StableHigherCurrentOrdinaryTerminal.Obstruction (preprocess (E.family G src)))

include negative in
theorem exists_label : ∃j : Fin (E.count G src),¬Product (fun x=>(E.table G src j x : AlgebraicComplex)) := by
  obtain ⟨f,hf,hp⟩ := negative.2.1
  obtain ⟨j,rfl⟩ := hf.1
  exact ⟨j,hp⟩

def label : Fin (E.count G src) := (exists_label G src negative).choose

theorem label_nonproduct : ¬Product (fun x=>(E.table G src (label G src negative) x : AlgebraicComplex)) :=
  (exists_label G src negative).choose_spec

abbrev arity := E.arity G src (label G src negative).val

def bundle : B.Choice (E.field G src) (E.table G src (label G src negative)) :=
  B.choose _ _ (label_nonproduct G src negative)

def blocks : D.Recipe (u:=1) (s:=E.count G src) (a:=fun _=>arity G src negative+0)
    (b:=E.arity G src) :=
  R.recipe (label G src negative) (bundle G src negative).rows

theorem balanced : D.EvenRecipe (blocks G src negative) :=
  R.even_recipe _ _ (bundle G src negative).even

def row : Signature (E.field G src) (arity G src negative) :=
  D.trace (E.table G src) 0 (blocks G src negative) 0

theorem row_value (x : Fin (arity G src negative)→Bool) :
    row G src negative x=(bundle G src negative).coefficient x := by
  have word (y : Fin 0→Bool) : Fin.addCases (m:=arity G src negative) (n:=0) x y=x := by
    funext j
    exact Fin.addCases_left (m:=arity G src negative) (n:=0) (motive:=fun _=>Bool) (left:=x) (right:=y) j
  change (∑y : Fin 0→Bool,D.coefficient (E.table G src) (blocks G src negative) 0 (Fin.addCases x y))=_
  simp_rw [word]
  simp only [blocks,R.coefficient_eq]
  simp [OrdinaryNegativeNonproductBundleChoice.Choice.coefficient]

theorem row_nonproduct : ¬Product (fun x=>(row G src negative x : AlgebraicComplex)) := by
  simpa only [row_value,OrdinaryNegativeNonproductBundleChoice.Choice.coefficient] using (bundle G src negative).nonproduct

def AllClosed : Prop := ∀j : Fin (E.count G src),C.Closed (fun x=>(E.table G src j x : AlgebraicComplex))

theorem row_closed (h : AllClosed G src) : C.Closed (fun x=>(row G src negative x : AlgebraicComplex)) := by
  simpa only [row_value] using C.nonproduct_choice_closed (E.field G src)
    (E.table G src (label G src negative)) (bundle G src negative) (h _)

theorem rows_bound : (bundle G src negative).rows.length≤16 := (bundle G src negative).length

/-- The chosen row, recipe and unchanged original-G programme are outputs. -/
def source := PhysicalProgramme.ofControlled (Programme.compose
  (R.controlled (label G src negative) (bundle G src negative).rows
    (E.table G src) (E.presentation G src) (E.eq4Label G src)
    (E.pinLabel G src false) (E.pinLabel G src true) (E.eq4_literal G src)
    (E.pin_literal G src false) (E.pin_literal G src true) (bundle G src negative).even)
  (E.ordinarySource G src))

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeGenericXNonproduct
end
