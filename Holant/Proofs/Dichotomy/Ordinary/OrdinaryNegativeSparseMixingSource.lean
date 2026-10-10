import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeSparseMixingPositive
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeSparseMixingUnary
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeSparseMixingThreeSeven
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeMixedBlockRelabel
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeMixedBlockSource

/-! Fixed-field actual-label versions of all small-rank mixing recipes.
Per-label sigma equalities preserve the original table and its exact scales.
Every returned block has its literal even-incidence proof and its compiled
private-sum source into that unchanged table, using actual Eq4 and both pins.
No physical realization of a semantic compressed row is assumed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeSparseMixingSource
open Computability Holant Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open OrdinaryNegativeMixedBlockData
open scoped BigOperators
namespace R
export OrdinaryNegativeMixedBlockRelabel (exactRecipe even_recipe coefficient_eq)
end R
namespace M
export OrdinaryNegativeMixedBlockSource (trace privateValue privateControlled)
end M
namespace X
export OrdinaryNegativeSparseMixingX (arity recipe even_recipe table trace_value scaled_trace)
end X
namespace P
export OrdinaryNegativeSparseMixingPositive (recipe even_recipe table mixed value scaled_value)
end P
namespace U
export OrdinaryNegativeSparseMixingUnary (arity recipe even_recipe table mixed value scaled_value)
end U
namespace T
export OrdinaryNegativeSparseMixingThreeSeven (arity recipe even_recipe table mixed value scaled_value)
end T
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false

variable {K : Type} [Field K] [Algebra ℚ K] {s : ℕ} {b : ℕ→ℕ}
variable (H : (j : Fin s)→Signature K (b j.val))

structure Block (n : ℕ) where
  privateCount : ℕ
  rows : Recipe (u:=1) (s:=s) (a:=fun _=>n+privateCount) (b:=b)
  balanced : EvenRecipe rows

namespace Block
variable {n : ℕ}
def signature (B : Block (s:=s) (b:=b) n) : Signature K n :=
  M.trace H B.privateCount B.rows 0

variable {d : ℕ} (F : FixedField K d) (e p0 p1 : Fin s)
variable (he : (⟨b e.val,H e⟩ : AnySignature K)=⟨4,Holant.EightVertex.ProductAnchor.equalityFour⟩)
variable (h0 : (⟨b p0.val,H p0⟩ : AnySignature K)=⟨1,Holant.LocalDrafts.RemoteWork.CountingBridge.Gates.pin false⟩)
variable (h1 : (⟨b p1.val,H p1⟩ : AnySignature K)=⟨1,Holant.LocalDrafts.RemoteWork.CountingBridge.Gates.pin true⟩)

def controlled (B : Block (s:=s) (b:=b) n) :=
  M.privateControlled F H e p0 p1 he h0 h1 B.privateCount B.rows B.balanced

def physical (B : Block (s:=s) (b:=b) n) :=
  PhysicalProgramme.ofControlled (controlled H F e p0 p1 he h0 h1 B)
end Block

variable (labels : Fin 2→Fin s)

def literal {a : ℕ→ℕ} (T : (i : Fin 2)→Signature K (a i.val)) : Prop :=
  ∀i,(⟨b (labels i).val,H (labels i)⟩ : AnySignature K)=⟨a i.val,T i⟩

variable {n : ℕ}
def xBlock (f : Signature K n) (d : K) (h : literal H labels (X.table f d)) :
    Block (s:=s) (b:=b) n where
  privateCount := n
  rows := R.exactRecipe labels (X.table f d) H h (X.recipe n)
  balanced := R.even_recipe labels (fun i=>congrArg Sigma.fst (h i)) _ (X.even_recipe n)

theorem x_value (f : Signature K n) (d : K) (h : literal H labels (X.table f d))
    (x : Fin n→Bool) : (xBlock H labels f d h).signature H x=d^n*f x := by
  unfold Block.signature xBlock M.trace
  simp_rw [R.coefficient_eq]
  exact X.trace_value f d x

theorem x_scaled_value (f : Signature K n) (c d : K)
    (h : literal H labels (X.table (fun x=>c*f x) d)) (x : Fin n→Bool) :
    (xBlock H labels (fun x=>c*f x) d h).signature H x=(c*d^n)*f x := by
  rw [x_value]
  ring

theorem trace_zero (rs : Recipe (u:=1) (s:=s) (a:=fun _=>n) (b:=b))
    (x : Fin n→Bool) : M.trace H 0 rs 0 x=coefficient H rs 0 x := by
  classical
  unfold M.trace
  rw [Fintype.sum_unique]
  congr 1
  funext i
  change Fin.addCases x _ (Fin.castAdd 0 i)=x i
  rw [Fin.addCases_left]

def positiveBlock (f g : Signature K n) (h : literal (a:=fun _=>n) H labels (P.table f g)) :
    Block (s:=s) (b:=b) n where
  privateCount := 0
  rows := R.exactRecipe (b:=fun _=>n) labels (P.table f g) H h (P.recipe n)
  balanced := R.even_recipe labels (fun i=>congrArg Sigma.fst (h i)) _ (P.even_recipe n)

theorem positive_value (f g : Signature K n) (h : literal (a:=fun _=>n) H labels (P.table f g))
    (x : Fin n→Bool) : (positiveBlock H labels f g h).signature H x=f x*g x := by
  unfold Block.signature positiveBlock
  rw [trace_zero,R.coefficient_eq]
  exact P.value f g x

def unaryBlock (f : Signature K n) (u : Signature K 1) (h : literal H labels (U.table f u)) :
    Block (s:=s) (b:=b) n where
  privateCount := 0
  rows := R.exactRecipe labels (U.table f u) H h (U.recipe n)
  balanced := R.even_recipe labels (fun i=>congrArg Sigma.fst (h i)) _ (U.even_recipe n)

theorem unary_value (f : Signature K n) (u : Signature K 1) (h : literal H labels (U.table f u))
    (x : Fin n→Bool) : (unaryBlock H labels f u h).signature H x=U.mixed f u x := by
  unfold Block.signature unaryBlock
  rw [trace_zero,R.coefficient_eq]
  rfl

def threeSevenBlock (f : Signature K 7) (g : Signature K 3) (h : literal H labels (T.table f g)) :
    Block (s:=s) (b:=b) 7 where
  privateCount := 0
  rows := R.exactRecipe labels (T.table f g) H h T.recipe
  balanced := R.even_recipe labels (fun i=>congrArg Sigma.fst (h i)) _ T.even_recipe

theorem threeSeven_value (f : Signature K 7) (g : Signature K 3) (h : literal H labels (T.table f g))
    (x : Fin 7→Bool) : (threeSevenBlock H labels f g h).signature H x=T.mixed f g x := by
  unfold Block.signature threeSevenBlock
  rw [trace_zero,R.coefficient_eq]
  rfl

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeSparseMixingSource
end
