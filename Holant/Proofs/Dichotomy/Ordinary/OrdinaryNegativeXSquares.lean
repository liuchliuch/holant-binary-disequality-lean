import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeXNonproduct
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeMixedBlockResourcesXOriginal

/-! A rejected ordinary family either has an actual counting-hard source or
all literal pointwise squares are Affine. The squared row is emitted twice,
and the incompatible non-Product resource is internally chosen from the same
obstruction; no support-closure or successful-gadget backend is supplied. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeXSquares
open Computability Holant Holant.Tractable Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace E
export GlobalCloseCompletionEq4FullSource (count arity table family)
export GlobalCloseCompletionEq4CSPSource (field)
end E
namespace N
export OrdinaryNegativeXNonproduct (blocks balanced row row_nonproduct)
end N
namespace B
export OrdinaryNegativeNonproductBundleChoice (duplicate duplicate_even duplicate_value)
end B
namespace R
export OrdinaryNegativeNonproductBundleSource (recipe even_recipe coefficient_eq)
end R
namespace D
export OrdinaryNegativeMixedBlockData (Recipe EvenRecipe coefficient)
export OrdinaryNegativeMixedBlockSource (trace)
end D
namespace H
export OrdinaryNegativeMixedBlockResourcesXOriginal (source countingHard)
end H
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
variable (j : Fin (E.count G P))

def blocks : D.Recipe (u:=1) (s:=E.count G P) (a:=fun _=>E.arity G P o j.val+0)
    (b:=E.arity G P o) := R.recipe j B.duplicate

theorem balanced : D.EvenRecipe (blocks G P o j) := R.even_recipe _ _ B.duplicate_even

def row : Signature (E.field G P o) (E.arity G P o j.val) :=
  D.trace (E.table G P o) 0 (blocks G P o j) 0

theorem row_value (x : Fin (E.arity G P o j.val)→Bool) : row G P o j x=E.table G P o j x^2 := by
  have word (y : Fin 0→Bool) : Fin.addCases (m:=E.arity G P o j.val) (n:=0) x y=x := by
    funext q
    exact Fin.addCases_left (m:=E.arity G P o j.val) (n:=0) (motive:=fun _=>Bool) (left:=x) (right:=y) q
  change (∑y : Fin 0→Bool,D.coefficient (E.table G P o) (blocks G P o j) 0 (Fin.addCases x y))=_
  simp_rw [word]
  simp only [blocks,R.coefficient_eq,B.duplicate_value]
  simp

abbrev Hard : Prop := Holant.LocalDrafts.CountingHardness.WitnessCountingHard
  (OriginalForestSource.inputEncoding (s:=s) (arity:=a))
  (OriginalForestSource.presentation G).encoding (OriginalForestSource.value G)

variable (bad : ¬Affine (fun x=>(E.table G P o j x : AlgebraicComplex)^2))

include bad in
theorem row_nonaffine : ¬Affine (fun x=>(row G P o j x : AlgebraicComplex)) := by
  have he (x : Fin (E.arity G P o j.val)→Bool) :
      (row G P o j x : AlgebraicComplex)=(E.table G P o j x : AlgebraicComplex)^2 := by
    rw [row_value]
    exact map_pow (E.field G P o).subtype _ 2
  simpa only [he] using bad

variable {α : Type} {ea : Encoding α Bool} {count : α→ℕ}

def source (w : SharpPWitness ea count) :=
  H.source G P o (blocks G P o j) (N.blocks G P o negative)
    (row_nonaffine G P o j bad) (N.row_nonproduct G P o negative)
    (balanced G P o j) (N.balanced G P o negative) w

include negative bad in
theorem countingHard : Hard G :=
  H.countingHard G P o (blocks G P o j) (N.blocks G P o negative)
    (row_nonaffine G P o j bad) (N.row_nonproduct G P o negative)
    (balanced G P o j) (N.balanced G P o negative)

def AllSquaresAffine : Prop := ∀j : Fin (E.count G P),
  Affine (fun x=>(E.table G P o j x : AlgebraicComplex)^2)

include negative in
theorem all_squares_or_countingHard : AllSquaresAffine G P o ∨ Hard G := by
  classical
  by_cases h : AllSquaresAffine G P o
  · exact Or.inl h
  · change ¬∀j : Fin (E.count G P),Affine (fun x=>(E.table G P o j x : AlgebraicComplex)^2) at h
    obtain ⟨j,hj⟩ := not_forall.mp h
    exact Or.inr (countingHard G P o negative j hj)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeXSquares
end
