import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeMixedBlockLiteral
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeOcticFourierRecipeSemantics

/-! Literal opposite-bundle overlay. Both physical input rows retain every
coefficient and every port. The shared negative ports have one unique private
assignment, giving the unsquared product on the surviving doubled variables.
This is the equal-size and rank-one ingredient of Cai--Lu--Xia, Lemma 4.17:
https://arxiv.org/html/1702.02693#S4.SS7 -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeSparseMixingCore
open Holant Holant.Tractable
open OrdinaryNegativeMixedBlockData
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
variable {K : Type} [CommSemiring K] {n : ℕ}

def positive (x : Fin (n+n)→Bool) : Fin n→Bool := fun i=>x (Fin.castAdd n i)
def negative (x : Fin (n+n)→Bool) : Fin n→Bool := fun i=>x (Fin.natAdd n i)
def opposite (f : Signature K n) : Signature K (n+n) := fun x=>
  if negative x=(fun i=>!(positive x i)) then f (positive x) else 0

def same (f : Signature K n) : Signature K (n+n) := fun x=>
  if negative x=positive x then f (positive x) else 0

theorem opposite_addCases (f : Signature K n) (x y : Fin n→Bool) :
    opposite f (Fin.addCases x y)=if y=(fun i=>!(x i)) then f x else 0 := by
  have hp : positive (Fin.addCases x y)=x := by funext i; simp [positive]
  have hn : negative (Fin.addCases x y)=y := by
    funext i
    change Fin.addCases x y (Fin.natAdd n i)=y i
    rw [Fin.addCases_right]
  rw [opposite,hp,hn]

def overlay (g h : Signature K (n+n)) : Signature K n := fun x=>
  ∑y : Fin n→Bool,g (Fin.addCases x y)*h (Fin.addCases x y)

theorem overlay_value (f g : Signature K n) (x : Fin n→Bool) :
    overlay (opposite f) (opposite g) x=f x*g x := by
  classical
  unfold overlay
  simp only [opposite_addCases]
  calc
    _=∑y : Fin n→Bool,if y=(fun i=>!(x i)) then f x*g x else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      split_ifs <;> simp
    _=_ := by simp

/-- Two actual rows, with one occurrence of each positive and negative port
per row. Identification of corresponding external variables gives even degree. -/
def overlayRecipe (n : ℕ) : Recipe (u:=1) (s:=2) (a:=fun _=>n+n) (b:=fun _=>n+n) :=
  fun _=>[⟨0,Sum.inr⟩,⟨1,Sum.inr⟩]

theorem overlay_even (n : ℕ) : EvenRecipe (overlayRecipe n) := by
  intro i q
  simp only [ports,overlayRecipe,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.count_append]
  exact ⟨_,rfl⟩

def overlayTable (g h : Signature K (n+n)) (i : Fin 2) : Signature K (n+n) :=
  if i.val=0 then g else h

theorem overlay_coefficient (g h : Signature K (n+n)) (x : Fin (n+n)→Bool) :
    coefficient (overlayTable g h) (overlayRecipe n) 0 x=g x*h x := by
  simp [coefficient,Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyBundleValue.coefficient,
    overlayRecipe,overlayTable]

theorem literal_overlay (f g : Signature K n) (x : Fin n→Bool) :
    (∑y : Fin n→Bool,coefficient (overlayTable (opposite f) (opposite g))
      (overlayRecipe n) 0 (Fin.addCases x y))=f x*g x := by
  simp_rw [overlay_coefficient]
  exact overlay_value f g x

/-- The two original normalization coefficients multiply, rather than
being discarded by the bundle picture. -/
theorem scaled_overlay (f g : Signature K n) (c d : K) (x : Fin n→Bool) :
    overlay (opposite (fun x=>c*f x)) (opposite (fun x=>d*g x)) x=
      (c*d)*(f x*g x) := by
  rw [overlay_value]
  ring

def unary (a b : K) : Signature K 1 := fun x=>if x 0 then b else a

theorem rankOne_value (a b c d : K) (x : Fin 1→Bool) :
    overlay (opposite (unary a b)) (opposite (unary c d)) x=unary (a*c) (b*d) x := by
  rw [overlay_value]
  cases hx : x 0 <;> simp [unary,hx]

/-- Mixing an affine rank-one ratio with an octic rank-one ratio really
leaves the affine class. Both source scales remain in the computed row. -/
theorem rankOne_not_affine (a b c d : AlgebraicComplex)
    (ha : a≠0) (hc : c≠0) (hab : b^4=a^4) (hcd : d^4= -(c^4)) :
    ¬Affine (overlay (opposite (unary a b)) (opposite (unary c d))) := by
  have hb : b≠0 := by intro h; rw [h,zero_pow (by decide)] at hab; exact pow_ne_zero 4 ha hab.symm
  have hd : d≠0 := by
    intro h
    have hz : c^4=0 := by simpa [h] using hcd.symm
    exact pow_ne_zero 4 hc hz
  intro h
  have he := h.fourth_power_eq (x:=fun _=>false) (y:=fun _=>true)
    (by simpa only [rankOne_value,unary,Bool.false_eq_true,ite_false] using mul_ne_zero ha hc)
    (by simpa only [rankOne_value,unary,ite_true] using mul_ne_zero hb hd)
  simp only [rankOne_value,unary,Bool.false_eq_true,ite_false,ite_true,mul_pow,hab,hcd] at he
  have hn : a^4*c^4≠0 := mul_ne_zero (pow_ne_zero _ ha) (pow_ne_zero _ hc)
  apply hn
  linear_combination he/2

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeSparseMixingCore
end
