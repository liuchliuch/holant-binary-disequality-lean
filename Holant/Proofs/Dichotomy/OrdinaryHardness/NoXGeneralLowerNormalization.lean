import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralLatticeSupport
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeAffineSupportExtraction

/-! A supported coordinatewise lower bound can be normalized to the origin
by literal pin-one substitutions. The coordinates changed this way are fixed
on the entire support; explicit unary masks recover the original row. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralLowerNormalization
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open scoped BigOperators
namespace L
export NoXGeneralLatticeSupport (Below)
end L
namespace T
export GeneralEOPairedFamilyExtractionTensor (substitute)
end T
namespace C
export GeneralEONegativeClosedSupport (Closed)
end C
namespace B
export OrdinaryNegativeSparseMixingSource (Block)
end B
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 32768
set_option Elab.async false
attribute [local instance] Classical.propDecidable
variable {n : ℕ}
def ports (lo : Word n) : Fin n→Bool ⊕ Fin n := fun i=>if lo i then .inl true else .inr i

def fill (lo x : Word n) : Word n := T.substitute (ports lo) x

def normalized {K : Type*} (f : Signature K n) (lo : Word n) : Signature K n := fun x=>f (fill lo x)

theorem fill_origin (lo : Word n) : fill lo (origin n)=lo := by
  funext i
  cases hi : lo i <;> simp [fill,T.substitute,ports,origin,hi]

theorem fill_eq (lo x : Word n) (bound : L.Below lo x) : fill lo x=x := by
  funext i
  have h:=bound i
  cases hl : lo i <;> cases hx : x i <;> simp_all [fill,T.substitute,ports]

theorem fill_triple (lo x y z : Word n) :
    fill lo (tripleXor x y z)=tripleXor (fill lo x) (fill lo y) (fill lo z) := by
  funext i
  cases hl : lo i <;> cases hx : x i <;> cases hy : y i <;> cases hz : z i <;>
    simp [fill,T.substitute,ports,tripleXor,hl,hx,hy,hz]

def mask (lo : Word n) : Signature AlgebraicComplex n :=
  fun x=>∏i,if lo i then (if x i then 1 else 0) else 1

theorem mask_value (lo x : Word n) : mask lo x=if L.Below lo x then 1 else 0 := by
  classical
  by_cases bound : L.Below lo x
  · rw [ite_eq_left bound]
    apply Finset.prod_eq_one
    intro i _
    have h:=bound i
    cases hl : lo i <;> cases hx : x i <;> simp_all
  · rw [ite_eq_right bound]
    change (∏i,if lo i then (if x i then (1 : AlgebraicComplex) else 0) else 1)=0
    unfold L.Below at bound
    push Not at bound
    obtain ⟨i,hl,hx⟩ := bound
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hl,hx]

def system (lo : Word n) : AffineSystem n where
  rows := n
  matrix i j := if j=i then bitValue (ZMod 2) (lo i) else 0
  rhs i := bitValue (ZMod 2) (lo i)

theorem system_holds (lo x : Word n) : (system lo).Holds x ↔ L.Below lo x := by
  simp only [AffineSystem.Holds,system,ite_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  apply forall_congr'
  intro i
  cases hl : lo i <;> cases hx : x i <;> norm_num [bitValue]

theorem mask_affine (lo : Word n) : Affine (mask lo) := by
  convert (affine_constant n 1).restrict (system lo) using 1
  funext x
  simp only [mask_value,system_holds]

theorem mask_product (lo : Word n) : Product (mask lo) := by
  have h (s : Finset (Fin n)) : Product (fun x : Word n=>∏i∈s,if lo i then (if x i then 1 else 0) else 1) := by
    induction s using Finset.induction_on with
    | empty=>simpa using product_constant n 1
    | @insert i s hi ih=>
        have one : Product (fun x : Word n=>if lo i then (if x i then 1 else 0) else 1) :=
          product_unary i (fun b=>if lo i then (if b then 1 else 0) else 1)
        simpa only [Finset.prod_insert hi] using one.mul ih
  exact h Finset.univ

variable (f : Signature AlgebraicComplex n) (lo : Word n)
variable (bound : ∀x,f x≠0→L.Below lo x)

include bound in
theorem recover : f=fun x=>mask lo x*normalized f lo x := by
  funext x
  rw [mask_value]
  by_cases hx : L.Below lo x
  · rw [ite_eq_left hx,one_mul]
    exact congrArg f (fill_eq lo x hx).symm
  · rw [ite_eq_right hx,zero_mul]
    by_contra live
    exact hx (bound x live)

include bound in
theorem nonaffine (bad : ¬Affine f) : ¬Affine (normalized f lo) := by
  intro good
  apply bad
  rw [recover f lo bound]
  exact (mask_affine lo).mul good

include bound in
theorem nonproduct (bad : ¬Product f) : ¬Product (normalized f lo) := by
  intro good
  apply bad
  rw [recover f lo bound]
  exact (mask_product lo).mul good

theorem closed (h : C.Closed f) : C.Closed (normalized f lo) := by
  intro x y z hx hy hz
  unfold normalized
  rw [fill_triple]
  exact h _ _ _ hx hy hz

section Physical
variable {K : Type} [Field K] {s : ℕ} {b : ℕ→ℕ}
variable (row : B.Block (s:=s) (b:=b) n)
def block (lo : Word n) : B.Block (s:=s) (b:=b) n := NoXGeneralUnsignedBinary.restrict row (ports lo)

theorem value (H : (i : Fin s)→Signature K (b i.val)) (lo : Word n) (x : Word n) :
    (block row lo).signature H x=normalized (row.signature H) lo x :=
  NoXGeneralUnsignedBinary.restrict_value row (ports lo) H x
end Physical


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralLowerNormalization
end
