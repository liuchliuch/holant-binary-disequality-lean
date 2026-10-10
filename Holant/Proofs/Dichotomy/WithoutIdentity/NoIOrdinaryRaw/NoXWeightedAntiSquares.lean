import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.GenericOrdinarySource
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoXNonproduct
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoXWeightedAntiResourcesOriginal
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.Target

/-! A rejected ordinary family with an actual full weighted antidiagonal either has an actual counting-hard source or
all literal pointwise squares are Affine. The squared row is emitted twice,
and the incompatible non-Product resource is internally chosen from the same
obstruction; no support-closure or successful-gadget backend is supplied. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIOrdinaryRaw.NoXWeightedAntiSquares
open Computability Holant Holant.Tractable Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace E
export NoIOrdinaryRaw.GenericOrdinarySource (count arity table family)
export NoIOrdinaryRaw.GenericOrdinarySource (field)
end E
namespace N
export NoIOrdinaryRaw.NoXNonproduct (blocks balanced row row_nonproduct)
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
export NoIOrdinaryRaw.NoXWeightedAntiResourcesOriginal (source countingHard)
end H
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : NoIOrdinaryRaw.Target)
variable (src : NoIOrdinaryRaw.GenericOrdinarySource.Data G)
local instance : Algebra ℚ (E.field G src) := (E.field G src).algebra'
variable (negative : StableHigherCurrentOrdinaryTerminal.Obstruction (preprocess (E.family G src)))
variable (antiLabel : Fin (E.count G src)) (v w : E.field G src)
variable (hv : v≠0) (hw : w≠0)
variable (ha_lit : (⟨E.arity G src antiLabel.val,E.table G src antiLabel⟩ : AnySignature (E.field G src))=
  ⟨2,NoXWeightedAntiSigned.anti v w⟩)
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

abbrev Hard : Prop := NoIOrdinaryRaw.Target.Hard G

variable (bad : ¬Affine (fun x=>(E.table G src j x : AlgebraicComplex)^2))

include bad in
theorem row_nonaffine : ¬Affine (fun x=>(row G src j x : AlgebraicComplex)) := by
  have he (x : Fin (E.arity G src j.val)→Bool) :
      (row G src j x : AlgebraicComplex)=(E.table G src j x : AlgebraicComplex)^2 := by
    rw [row_value]
    exact map_pow (E.field G src).subtype _ 2
  simpa only [he] using bad

variable {α : Type} {ea : Encoding α Bool} {count : α→ℕ}

def source (witness : SharpPWitness ea count) :=
  H.source G src antiLabel v w hv hw ha_lit (blocks G src j) (N.blocks G src negative)
    (row_nonaffine G src j bad) (N.row_nonproduct G src negative)
    (balanced G src j) (N.balanced G src negative) witness

include negative bad hv hw ha_lit in
theorem countingHard : Hard G :=
  H.countingHard G src antiLabel v w hv hw ha_lit (blocks G src j) (N.blocks G src negative)
    (row_nonaffine G src j bad) (N.row_nonproduct G src negative)
    (balanced G src j) (N.balanced G src negative)

def AllSquaresAffine : Prop := ∀j : Fin (E.count G src),
  Affine (fun x=>(E.table G src j x : AlgebraicComplex)^2)

include negative hv hw ha_lit in
theorem all_squares_or_countingHard : AllSquaresAffine G src ∨ Hard G := by
  classical
  by_cases h : AllSquaresAffine G src
  · exact Or.inl h
  · change ¬∀j : Fin (E.count G src),Affine (fun x=>(E.table G src j x : AlgebraicComplex)^2) at h
    obtain ⟨j,hj⟩ := not_forall.mp h
    exact Or.inr (countingHard G src negative antiLabel v w hv hw ha_lit j hj)

include ha_lit hv hw in
theorem anti_eighth_of_squares (squares : AllSquaresAffine G src) : v^8=w^8 := by
  have ht : (⟨E.arity G src antiLabel.val,E.table G src antiLabel⟩ : AnySignature (E.field G src))∈
      {f : AnySignature (E.field G src) | Affine (fun x=>(f.2 x : AlgebraicComplex)^2)} := squares antiLabel
  rw [ha_lit] at ht
  have sq : Affine (fun x=>(NoXWeightedAntiSigned.anti (K:=E.field G src) v w x : AlgebraicComplex)^2) := ht
  apply Subtype.ext
  have h := sq.fourth_power_eq (![false,true]) (![true,false])
    (by simp [NoXWeightedAntiSigned.anti,hv]) (by simp [NoXWeightedAntiSigned.anti,hw])
  simpa [NoXWeightedAntiSigned.anti,←pow_mul] using h

include negative hv hw ha_lit in
theorem anti_eighth_or_hard : v^8=w^8 ∨ Hard G := by
  rcases all_squares_or_countingHard G src negative antiLabel v w hv hw ha_lit with squares|hard
  · exact Or.inl (anti_eighth_of_squares G src antiLabel v w hv hw ha_lit squares)
  · exact Or.inr hard

include negative hv hw ha_lit in
theorem hard_of_anti_eighth_failure (bad : v^8≠w^8) : Hard G :=
  (anti_eighth_or_hard G src negative antiLabel v w hv hw ha_lit).resolve_left bad


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIOrdinaryRaw.NoXWeightedAntiSquares
end
