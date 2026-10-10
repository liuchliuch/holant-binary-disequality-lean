import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPurePhaseAnchorIncidence
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPurePhaseIncidenceTranslation
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPurePhaseRecipeFactor

/-! A fixed corrected-affine odd anchor gives a concrete obstruction recipe
for every incompatible rank-at-most-three test row. All six factors are
actual signed substitutions into one test row and one anchor row. The same
root and anchor are used throughout; no test-dependent phase is selected. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePhaseAnchorRecipe
open Holant Holant.Tractable
open NoIPurePhaseRecipeFactor (Port word)
open scoped BigOperators
namespace A
export NoIPurePhaseIncidenceCore.C (codeSeven)
theorem codeSeven_affine : TwoTranslate.IsAffineMap codeSeven := by
  unfold TwoTranslate.IsAffineMap
  decide
end A
namespace P
export NoIPurePhaseIncidencePorts.R (transformed transformed_word)
end P
namespace C
export NoIPurePhaseAnchorIncidence (schedule charge schedule_certificate)
export NoIPurePhaseIncidenceRegularization (pattern)
end C
namespace W
export NoIPurePhaseIncidenceWeight (residue)
export NoIPurePhaseRecipeFactor (incidence)
end W
namespace R
export NoIPurePhaseRecipeFactor (factor total mul_iff)
end R
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
set_option Elab.async false
variable {n m : ℕ}

def corrected (r : AlgebraicComplex) {l : ℕ} (f : Signature AlgebraicComplex l) :
    Signature AlgebraicComplex l := fun x=>r^(weight x)*f x

theorem word_affine {l k : ℕ} (p : Fin l→Port k) :
    TwoTranslate.IsAffineMap (word p) := by
  intro x y
  funext i
  cases h:p i with
  | inl b=>cases b <;> simp [word,h,AffinePhase.xor]
  | inr v=>
    rcases v with ⟨j,s⟩
    cases s <;> cases x j <;> cases y j <;> simp [word,h,AffinePhase.xor,AffinePhase.origin]

def anchorPort (q : Fin m→Port 7) (a t : ZMod 4) (u : Fin 3→Bool)
    (i : Fin 5) : Fin m→Port 7 :=
  match C.schedule a t u i with
  | none=>q
  | some v=>P.transformed q v

def arity (n m : ℕ) : Fin 6→ℕ := Fin.cases n (fun _=>m)

def rows (p : Fin n→Port 7) (q : Fin m→Port 7) (a t : ZMod 4) (u : Fin 3→Bool) :
    (i : Fin 6)→Fin (arity n m i)→Port 7 :=
  Fin.cases p (fun i=>anchorPort q a t u i)

def values (f : Signature AlgebraicComplex n) (g : Signature AlgebraicComplex m) :
    (i : Fin 6)→Signature AlgebraicComplex (arity n m i) :=
  Fin.cases f (fun _=>g)

def product (f : Signature AlgebraicComplex n) (g : Signature AlgebraicComplex m)
    (p : Fin n→Port 7) (q : Fin m→Port 7) (a t : ZMod 4) (u : Fin 3→Bool) :
    Signature AlgebraicComplex 7 :=
  fun z=>∏i : Fin 6,values f g i (word (rows p q a t u i) z)

theorem anchor_residue (q : Fin m→Port 7) (a t : ZMod 4) (u : Fin 3→Bool)
    (uniform : ∀j,W.residue q j=a) (i : Fin 5) (j : Fin 7) :
    W.residue (anchorPort q a t u i) j=C.charge a (C.schedule a t u i) j := by
  unfold anchorPort C.charge
  cases h:C.schedule a t u i with
  | none=>exact uniform j
  | some v=>
    rw [NoIPurePhaseIncidencePorts.transformed_residue]
    congr 1
    exact funext uniform

theorem rows_zero (p : Fin n→Port 7) (q : Fin m→Port 7) (a t : ZMod 4) (u : Fin 3→Bool)
    (odd : a=1 ∨ a=3) (uniform : ∀j,W.residue q j=a)
    (kernel : ∀j,W.residue p j=C.pattern t u j) (j : Fin 7) :
    R.total (rows p q a t u) j%4=0 := by
  have cast : (R.total (rows p q a t u) j : ZMod 4)=0 := by
    unfold R.total
    rw [Fin.sum_univ_succ]
    change ((W.incidence p j+∑i : Fin 5,W.incidence (anchorPort q a t u i) j : ℤ) : ZMod 4)=0
    simp only [Int.cast_add,Int.cast_sum]
    change W.residue p j+∑i : Fin 5,W.residue (anchorPort q a t u i) j=0
    simp_rw [anchor_residue q a t u uniform,kernel]
    exact C.schedule_certificate a t odd u j
  exact Int.emod_eq_zero_of_dvd ((ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mp cast)

theorem anchor_code_full (r : AlgebraicComplex) (rn : r≠0)
    (g : Signature AlgebraicComplex m) (q : Fin m→Port 7) (a t : ZMod 4) (u : Fin 3→Bool)
    (full : ∀x : Fin 3→Bool,g (word q (A.codeSeven x))≠0) (i : Fin 5) (x : Fin 3→Bool) :
    corrected r g (word (anchorPort q a t u i) (A.codeSeven x))≠0 := by
  apply mul_ne_zero (pow_ne_zero _ rn)
  unfold anchorPort
  cases h:C.schedule a t u i with
  | none=>exact full x
  | some v=>rw [P.transformed_word];exact full _

theorem corrected_product_value (r : AlgebraicComplex)
    (f : Signature AlgebraicComplex n) (g : Signature AlgebraicComplex m)
    (p : Fin n→Port 7) (q : Fin m→Port 7) (a t : ZMod 4) (u : Fin 3→Bool)
    (z : Fin 7→Bool) :
    product (corrected r f) (corrected r g) p q a t u z=
      product f g p q a t u z*R.factor (rows p q a t u) r z := by
  unfold product R.factor
  rw [←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  refine Fin.cases ?_ (fun j=>?_) i
  · simp only [values,rows,arity,Fin.cases_zero,corrected];ring
  · simp only [values,rows,arity,Fin.cases_succ,corrected];ring

theorem corrected_product_bad (r : AlgebraicComplex) (rn : r≠0)
    (f : Signature AlgebraicComplex n) (g : Signature AlgebraicComplex m)
    (p : Fin n→Port 7) (q : Fin m→Port 7) (a t : ZMod 4) (u : Fin 3→Bool)
    (anchor : Affine (corrected r g))
    (full : ∀x : Fin 3→Bool,g (word q (A.codeSeven x))≠0)
    (bad : ¬Affine (fun x : Fin 3→Bool=>corrected r f (word p (A.codeSeven x)))) :
    ¬Affine (product (corrected r f) (corrected r g) p q a t u) := by
  let multiplier : Signature AlgebraicComplex 7:=
    fun z=>∏i : Fin 5,corrected r g (word (anchorPort q a t u i) z)
  have good : Affine multiplier := by
    have h (s : Finset (Fin 5)) :
        Affine (fun z=>∏i∈s,corrected r g (word (anchorPort q a t u i) z)) := by
      induction s using Finset.induction_on with
      | empty=>simpa using affine_constant 7 1
      | @insert i s hi ih=>
        simpa only [Finset.prod_insert hi] using
          (anchor.precompose _ (word_affine (anchorPort q a t u i))).mul ih
    exact h Finset.univ
  have mfull (x : Fin 3→Bool) : multiplier (A.codeSeven x)≠0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _=>anchor_code_full r rn g q a t u full i x)
  intro affine
  have pull:=affine.precompose A.codeSeven A.codeSeven_affine
  apply bad
  apply (NoIPureAffineMultiplier.mul_iff _ _
    (good.precompose A.codeSeven A.codeSeven_affine) (fun x _=>mfull x)).mp
  simpa only [product,Fin.prod_univ_succ,values,rows,Fin.cases_zero,Fin.cases_succ,multiplier] using pull

/-- Exact six-row nonaffine certificate from one fixed common phase anchor. -/
theorem product_bad (r : AlgebraicComplex) (rn : r≠0) (root : r^16=1)
    (f : Signature AlgebraicComplex n) (g : Signature AlgebraicComplex m)
    (p : Fin n→Port 7) (q : Fin m→Port 7) (a t : ZMod 4) (u : Fin 3→Bool)
    (odd : a=1 ∨ a=3) (uniform : ∀j,W.residue q j=a)
    (kernel : ∀j,W.residue p j=C.pattern t u j)
    (anchor : Affine (corrected r g))
    (full : ∀x : Fin 3→Bool,g (word q (A.codeSeven x))≠0)
    (bad : ¬Affine (fun x : Fin 3→Bool=>corrected r f (word p (A.codeSeven x)))) :
    ¬Affine (product f g p q a t u) := by
  intro affine
  have good:=(R.mul_iff (rows p q a t u) r rn root
    (rows_zero p q a t u odd uniform kernel) (product f g p q a t u)).mpr affine
  have equal : (fun z=>product f g p q a t u z*R.factor (rows p q a t u) r z)=
      product (corrected r f) (corrected r g) p q a t u :=
    funext (fun z=>(corrected_product_value r f g p q a t u z).symm)
  rw [equal] at good
  exact corrected_product_bad r rn f g p q a t u anchor full bad good


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePhaseAnchorRecipe
end
