import Holant.Proofs.Hardness.GeneralEOPairedFamilyExtractionComponents
import Holant.Proofs.Hardness.GeneralEOPairedFamilyExtractionFullSupport

/-! Full-support reconstruction of an arbitrary intersection-closed linear
support. The internally selected representative of each support-column class
provides an actual identification/false-pin restriction. Both semantic class
failures reflect to that full-support restriction. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionComponentsFull
open Holant Holant.Tractable GeneralEOPairedFamilyExtractionSupport
open GeneralEOPairedFamilyExtractionComponents
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (f : Signature AlgebraicComplex n)

def column (i : Fin n) : Finset (Fin n) := Finset.univ.filter (Same f i)

theorem column_nonempty (i : Fin n) : (column f i).Nonempty :=
  ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,same_refl f i⟩⟩

def representative (i : Fin n) : Fin n := (column f i).min' (column_nonempty f i)

theorem same_representative (i : Fin n) : Same f i (representative f i) :=
  (Finset.mem_filter.mp (Finset.min'_mem (column f i) (column_nonempty f i))).2

theorem representative_eq {i j : Fin n} (h : Same f i j) :
    representative f i=representative f j := by
  have he : column f i=column f j := by
    ext k
    simp only [column,Finset.mem_filter,Finset.mem_univ,true_and]
    exact ⟨fun h' => same_trans f (same_symm f h) h',fun h' => same_trans f h h'⟩
  unfold representative
  simp only [he]

theorem active_iff {i j : Fin n} (h : Same f i j) : Active f i ↔ Active f j := by
  constructor
  · rintro ⟨w,hw,hi⟩
    exact ⟨w,hw,(h w hw).symm.trans hi⟩
  · rintro ⟨w,hw,hj⟩
    exact ⟨w,hw,(h w hw).trans hj⟩

def expand (x : Fin n → Bool) : Fin n → Bool :=
  fun i => if Active f i then x (representative f i) else false

def substitution (i : Fin n) : Bool ⊕ Fin n :=
  if Active f i then Sum.inr (representative f i) else Sum.inl false

theorem expand_substitute (x : Fin n → Bool) :
    expand f x=GeneralEOPairedFamilyExtractionTensor.substitute (substitution f) x := by
  funext i
  simp only [expand,substitution,GeneralEOPairedFamilyExtractionTensor.substitute]
  split_ifs <;> rfl

def reduced : Signature AlgebraicComplex n := fun x => f (expand f x)

theorem expand_supported (h0 : f origin≠0) (hx : XorClosed f) (hm : MeetClosed f)
    (x : Fin n → Bool) : f (expand f x)≠0 := by
  apply (support_iff f hx h0 hm _).mpr
  constructor
  · intro i hi
    by_contra hn
    simp [expand,hn] at hi
  · intro i j hs
    have ha := active_iff f hs
    have hr := representative_eq f hs
    simp only [expand,ha,hr]

theorem reduced_full (h0 : f origin≠0) (hx : XorClosed f) (hm : MeetClosed f) :
    ∀x,reduced f x≠0 := expand_supported f h0 hx hm

theorem expand_fixed (x : Fin n → Bool) (hx : f x≠0) : expand f x=x := by
  funext i
  by_cases ha : Active f i
  · simpa only [expand,ha,ite_true] using (same_representative f i x hx).symm
  · have hi : x i=false := by
      cases he : x i with
      | false => rfl
      | true => exact False.elim (ha ⟨x,hx,he⟩)
    simp [expand,ha,hi]

def Compatible (x : Fin n → Bool) : Prop := ∀i,x i=expand f x i

def indicator : Signature AlgebraicComplex n := fun x => if Compatible f x then 1 else 0

theorem reconstruction : f=fun x => reduced f x*indicator f x := by
  funext x
  by_cases hx : Compatible f x
  · have he : expand f x=x := funext fun i => (hx i).symm
    simp [reduced,indicator,hx,he]
  · have hz : f x=0 := by
      by_contra hn
      exact hx (fun i => (congrFun (expand_fixed f x hn) i).symm)
    simp [indicator,hx,hz]

def factor (i : Fin n) : ProductFactor n :=
  if Active f i then .equality i (representative f i)
  else .unary i (fun b => if b then 0 else 1) (by
    intro h
    have hh := congrFun h false
    norm_num at hh)

theorem factor_eval (i : Fin n) (x : Fin n → Bool) :
    (factor f i).eval x=if x i=expand f x i then 1 else 0 := by
  by_cases ha : Active f i
  · simp [factor,expand,ha,ProductFactor.eval,Signature.equality]
  · cases hi : x i <;> simp [factor,expand,ha,ProductFactor.eval,hi]

theorem indicator_product : Product (indicator f) := by
  convert product_formula 1 (List.ofFn (factor f)) using 1
  funext x
  simp only [productFormula,List.map_ofFn,List.prod_ofFn,one_mul,Function.comp_apply,factor_eval]
  by_cases hx : Compatible f x
  · have hh : ∀i,x i=expand f x i := hx
    simp [indicator,hx,hh]
  · obtain ⟨i,hi⟩ := not_forall.mp hx
    rw [show indicator f x=0 by simp [indicator,hx]]
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

def system : AffineSystem n where
  rows := n
  matrix i j := (if j=i then 1 else 0)+
    (if Active f i then (if j=representative f i then 1 else 0) else 0)
  rhs _ := 0

theorem system_holds (x : Fin n → Bool) : (system f).Holds x ↔ Compatible f x := by
  unfold AffineSystem.Holds Compatible
  apply forall_congr'
  intro i
  simp only [system,add_mul,Finset.sum_add_distrib,ite_mul,one_mul,zero_mul]
  by_cases ha : Active f i
  · simp only [ite_true,Finset.sum_ite_eq',Finset.mem_univ,ite_true,expand,ha]
    cases x i <;> cases x (representative f i) <;> decide
  · simp only [ite_false,Finset.sum_ite_eq',Finset.mem_univ,ite_true,expand,ha,Finset.sum_const_zero,add_zero]
    cases x i <;> decide

theorem indicator_affine : Affine (indicator f) := by
  change Affine (fun x => if Compatible f x then (1 : AlgebraicComplex) else 0)
  simpa only [system_holds] using affine_indicator (system f)

theorem product_of_reduced (h : Product (reduced f)) : Product f := by
  rw [reconstruction f]
  exact h.mul (indicator_product f)

theorem affine_of_reduced (h : Affine (reduced f)) : Affine f := by
  rw [reconstruction f]
  exact h.mul (indicator_affine f)

/-- Both failures survive the same literal constant/identification minor.
Its arity is unchanged; unused input coordinates do not affect full support. -/
theorem reduced_failures (ha : ¬Affine f) (hp : ¬Product f) :
    ¬Affine (reduced f) ∧ ¬Product (reduced f) :=
  ⟨fun h => ha (affine_of_reduced f h),fun h => hp (product_of_reduced f h)⟩

theorem exists_nonproduct_face (h0 : f origin≠0) (hx : XorClosed f)
    (hm : MeetClosed f) (hp : ¬Product f) :
    ∃i j : Fin n,i≠j ∧ ∃x : Fin n → Bool,
      EOBinaryPlaneClassification.Full (GeneralEOPairedFamilyExtractionFullSupport.face (reduced f) i j x) ∧
      ¬Product (GeneralEOPairedFamilyExtractionFullSupport.face (reduced f) i j x) :=
  GeneralEOPairedFamilyExtractionFullSupport.exists_nonproduct_face (reduced f)
    (reduced_full f h0 hx hm) (fun h => hp (product_of_reduced f h))

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionComponentsFull
