import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeXUniversalMixing
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXWeightedAntiOppositeCap

/-! Every port of both physical opposite resources remains in the doubled
positive mixer. Opposite pullback is a semantic test only. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXOppositeMixingLift
open Holant Holant.Tractable
open OrdinaryNegativeMixedBlockData
open OrdinaryNegativeXUniversalResource
open scoped BigOperators
namespace M
export OrdinaryNegativeXUniversalMixingCore (positiveRecipe unaryFirstRecipe unarySecondRecipe threeFirstRecipe threeSecondRecipe)
end M
namespace P
export OrdinaryNegativeXUniversalPair (arity table)
end P
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
set_option Elab.async false

def size (ka kb : Kind) : ℕ := max ka.arity kb.arity

def base (ka kb : Kind) : Recipe (u:=1) (s:=2) (a:=fun _=>size ka kb)
    (b:=P.arity ka.arity kb.arity) := by
  cases ka <;> cases kb
  · exact M.positiveRecipe 1
  · exact M.unaryFirstRecipe 3
  · exact M.unaryFirstRecipe 7
  · exact M.unarySecondRecipe 3
  · exact M.positiveRecipe 3
  · exact M.threeFirstRecipe
  · exact M.unarySecondRecipe 7
  · exact M.threeSecondRecipe
  · exact M.positiveRecipe 7

def liftPort {n : ℕ} (negative : Bool) : Bool ⊕ Fin n → Bool ⊕ Fin (n+n)
  | .inl bit=>.inl (if negative then !bit else bit)
  | .inr q=>.inr (if negative then Fin.natAdd n q else Fin.castAdd n q)

def lift {s n : ℕ} {b : ℕ→ℕ}
    (r : Recipe (u:=1) (s:=s) (a:=fun _=>n) (b:=b)) :
    Recipe (u:=1) (s:=s) (a:=fun _=>n+n) (b:=fun j=>b j+b j) :=
  fun i=>(r i).map (fun node=>⟨node.1,Fin.addCases
    (fun q=>liftPort false (node.2 q)) (fun q=>liftPort true (node.2 q))⟩)

theorem even (ka kb : Kind) : EvenRecipe (lift (base ka kb)) := by
  cases ka <;> cases kb <;> unfold EvenRecipe <;> decide

def opposite {n : ℕ} (x : Fin n→Bool) : Fin (n+n)→Bool := Fin.addCases x (fun q=>!(x q))

theorem opposite_affine (n : ℕ) : TwoTranslate.IsAffineMap (@opposite n) := by
  intro x y
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro q
    simp only [opposite,AffinePhase.xor,AffinePhase.origin,Fin.addCases_left]
    cases x q <;> cases y q <;> rfl
  · intro q
    simp only [opposite,AffinePhase.xor,AffinePhase.origin,Fin.addCases_right]
    cases x q <;> cases y q <;> rfl

variable {K : Type} [CommSemiring K] {s n : ℕ} {b : ℕ→ℕ}
variable (H : (j : Fin s)→Signature K (b j.val+b j.val))
def compressed (j : Fin s) : Signature K (b j.val) := fun x=>H j (opposite x)

theorem value (r : Recipe (u:=1) (s:=s) (a:=fun _=>n) (b:=b)) (x : Fin n→Bool) :
    coefficient H (lift r) 0 (opposite x)=coefficient (compressed H) r 0 x := by
  unfold coefficient Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyBundleValue.coefficient
  simp only [lift,List.map_map]
  congr 1
  apply List.map_congr_left
  intro node _
  change H node.1 _ = H node.1 _
  congr 1
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro q
    simp only [Fin.addCases_left,Fin.addCases_right]
    cases hp : node.2 q <;> simp only [hp,liftPort,Bool.false_eq_true,ite_false,ite_true,Sum.elim_inl,Sum.elim_inr,opposite,Fin.addCases_left,Fin.addCases_right,id_eq]
  · intro q
    simp only [Fin.addCases_left,Fin.addCases_right]
    cases hp : node.2 q <;> simp only [hp,liftPort,Bool.false_eq_true,ite_false,ite_true,Sum.elim_inl,Sum.elim_inr,opposite,Fin.addCases_left,Fin.addCases_right,id_eq]


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXOppositeMixingLift
end
