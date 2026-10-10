import Holant.Proofs.Dichotomy.General.GenericLiteralXSource
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeGenericXNonproduct
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeGenericXMixedBlockResourcesXOriginal

/-! A rejected ordinary family either has an actual counting-hard source or
all literal pointwise squares are Affine. The squared row is emitted twice,
and the incompatible non-Product resource is internally chosen from the same
obstruction; no support-closure or successful-gadget backend is supplied. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeGenericXSquares
open Computability Holant Holant.Tractable Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace E
export GenericLiteralXSource (count arity table family)
export GenericLiteralXSource (field)
end E
namespace N
export OrdinaryNegativeGenericXNonproduct (blocks balanced row row_nonproduct)
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
export OrdinaryNegativeGenericXMixedBlockResourcesXOriginal (source countingHard)
end H
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
variable (j : Fin (E.count G src))

def blocks : D.Recipe (u:=1) (s:=E.count G src) (a:=fun _=>E.arity G src j.val+0)
    (b:=E.arity G src) := R.recipe j B.duplicate

theorem balanced : D.EvenRecipe (blocks G src j) := R.even_recipe _ _ B.duplicate_even

def row : Signature (E.field G src) (E.arity G src j.val) :=
  D.trace (E.table G src) 0 (blocks G src j) 0

theorem row_value (x : Fin (E.arity G src j.val)→Bool) : row G src j x=E.table G src j x^2 := by
  have word (y : Fin 0→Bool) : Fin.addCases (m:=E.arity G src j.val) (n:=0) x y=x := by
    funext q
    exact Fin.addCases_left (m:=E.arity G src j.val) (n:=0) (motive:=fun _=>Bool) (left:=x) (right:=y) q
  change (∑y : Fin 0→Bool,D.coefficient (E.table G src) (blocks G src j) 0 (Fin.addCases x y))=_
  simp_rw [word]
  simp only [blocks,R.coefficient_eq,B.duplicate_value]
  simp

abbrev Hard : Prop := Holant.LocalDrafts.CountingHardness.WitnessCountingHard
  (OriginalForestSource.inputEncoding (s:=s) (arity:=a))
  (OriginalForestSource.presentation G).encoding (OriginalForestSource.value G)

variable (bad : ¬Affine (fun x=>(E.table G src j x : AlgebraicComplex)^2))

include bad in
theorem row_nonaffine : ¬Affine (fun x=>(row G src j x : AlgebraicComplex)) := by
  have he (x : Fin (E.arity G src j.val)→Bool) :
      (row G src j x : AlgebraicComplex)=(E.table G src j x : AlgebraicComplex)^2 := by
    rw [row_value]
    exact map_pow (E.field G src).subtype _ 2
  simpa only [he] using bad

variable {α : Type} {ea : Encoding α Bool} {count : α→ℕ}

def source (w : SharpPWitness ea count) :=
  H.source G src (blocks G src j) (N.blocks G src negative)
    (row_nonaffine G src j bad) (N.row_nonproduct G src negative)
    (balanced G src j) (N.balanced G src negative) w

include negative bad in
theorem countingHard : Hard G :=
  H.countingHard G src (blocks G src j) (N.blocks G src negative)
    (row_nonaffine G src j bad) (N.row_nonproduct G src negative)
    (balanced G src j) (N.balanced G src negative)

def AllSquaresAffine : Prop := ∀j : Fin (E.count G src),
  Affine (fun x=>(E.table G src j x : AlgebraicComplex)^2)

include negative in
theorem all_squares_or_countingHard : AllSquaresAffine G src ∨ Hard G := by
  classical
  by_cases h : AllSquaresAffine G src
  · exact Or.inl h
  · change ¬∀j : Fin (E.count G src),Affine (fun x=>(E.table G src j x : AlgebraicComplex)^2) at h
    obtain ⟨j,hj⟩ := not_forall.mp h
    exact Or.inr (countingHard G src negative j hj)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeGenericXSquares
end
