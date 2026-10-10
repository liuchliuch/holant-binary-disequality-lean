import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeNonproductBundleSource
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeAffineSupportClosure
import Holant.Proofs.Dichotomy.Closure.Eq4.GlobalCloseCompletionEq4FullSource

/-! The actual literal-X ordinary obstruction internally supplies its own
non-Product even resource. Closed support is inherited from the original row;
it is not supplied separately for the selected at-most-sixteen-row block. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeXNonproduct
open Computability Holant Holant.Tractable Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace E
export GlobalCloseCompletionEq4FullSource (count arity table family eq4Label pinLabel
  eq4_literal pin_literal ordinarySource)
export GlobalCloseCompletionEq4CSPSource (field presentation)
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
variable (P : Palette G) (o : GlobalCloseCompletionEq4Graph.Output G P)
local instance : Algebra ℚ (E.field G P o) := (E.field G P o).algebra'
variable (negative : StableHigherCurrentOrdinaryTerminal.Obstruction (preprocess (E.family G P o)))

include negative in
theorem exists_label : ∃j : Fin (E.count G P),¬Product (fun x=>(E.table G P o j x : AlgebraicComplex)) := by
  obtain ⟨f,hf,hp⟩ := negative.2.1
  obtain ⟨j,rfl⟩ := hf.1
  exact ⟨j,hp⟩

def label : Fin (E.count G P) := (exists_label G P o negative).choose

theorem label_nonproduct : ¬Product (fun x=>(E.table G P o (label G P o negative) x : AlgebraicComplex)) :=
  (exists_label G P o negative).choose_spec

abbrev arity := E.arity G P o (label G P o negative).val

def bundle : B.Choice (E.field G P o) (E.table G P o (label G P o negative)) :=
  B.choose _ _ (label_nonproduct G P o negative)

def blocks : D.Recipe (u:=1) (s:=E.count G P) (a:=fun _=>arity G P o negative+0)
    (b:=E.arity G P o) :=
  R.recipe (label G P o negative) (bundle G P o negative).rows

theorem balanced : D.EvenRecipe (blocks G P o negative) :=
  R.even_recipe _ _ (bundle G P o negative).even

def row : Signature (E.field G P o) (arity G P o negative) :=
  D.trace (E.table G P o) 0 (blocks G P o negative) 0

theorem row_value (x : Fin (arity G P o negative)→Bool) :
    row G P o negative x=(bundle G P o negative).coefficient x := by
  have word (y : Fin 0→Bool) : Fin.addCases (m:=arity G P o negative) (n:=0) x y=x := by
    funext j
    exact Fin.addCases_left (m:=arity G P o negative) (n:=0) (motive:=fun _=>Bool) (left:=x) (right:=y) j
  change (∑y : Fin 0→Bool,D.coefficient (E.table G P o) (blocks G P o negative) 0 (Fin.addCases x y))=_
  simp_rw [word]
  simp only [blocks,R.coefficient_eq]
  simp [OrdinaryNegativeNonproductBundleChoice.Choice.coefficient]

theorem row_nonproduct : ¬Product (fun x=>(row G P o negative x : AlgebraicComplex)) := by
  simpa only [row_value,OrdinaryNegativeNonproductBundleChoice.Choice.coefficient] using (bundle G P o negative).nonproduct

def AllClosed : Prop := ∀j : Fin (E.count G P),C.Closed (fun x=>(E.table G P o j x : AlgebraicComplex))

theorem row_closed (h : AllClosed G P o) : C.Closed (fun x=>(row G P o negative x : AlgebraicComplex)) := by
  simpa only [row_value] using C.nonproduct_choice_closed (E.field G P o)
    (E.table G P o (label G P o negative)) (bundle G P o negative) (h _)

theorem rows_bound : (bundle G P o negative).rows.length≤16 := (bundle G P o negative).length

/-- The chosen row, recipe and unchanged original-G programme are outputs. -/
def source := PhysicalProgramme.ofControlled (Programme.compose
  (R.controlled (label G P o negative) (bundle G P o negative).rows
    (E.table G P o) (E.presentation G P o) (E.eq4Label G P)
    (E.pinLabel G P false) (E.pinLabel G P true) (E.eq4_literal G P o)
    (E.pin_literal G P o false) (E.pin_literal G P o true) (bundle G P o negative).even)
  (E.ordinarySource G P o))

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeXNonproduct
end
