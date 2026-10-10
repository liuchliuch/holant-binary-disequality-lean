import Holant.EightVertex.ProductAnchor.ProductComponentsCut
import Holant.Proofs.FiniteGroups.Stabilization.FactorBaseChange

/-! Equality-component structure of the literal Product class, at arbitrary
arity. A disconnected constraint graph gives a genuine original-port split.
Consequently a Product prime has support in one complementary pair; there is
no restriction to binary components or to arity four. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionProductAncestorSupport
open Holant Holant.Tractable
open Holant.EightVertex.ProductAnchor
open Holant.LocalDrafts.FinitePGL2.Stabilization
open scoped BigOperators

variable {n : ℕ}

def cutPorts (C : Fin n → Bool) :
    (Fin (Fintype.card {i // C i = false}) ⊕
      Fin (Fintype.card {i // C i = true})) ≃ Fin n where
  toFun
    | .inl i => ((Fintype.equivFin {j // C j = false}).symm i).val
    | .inr i => ((Fintype.equivFin {j // C j = true}).symm i).val
  invFun i := if h : C i = false then
      .inl ((Fintype.equivFin {j // C j = false}) ⟨i,h⟩)
    else .inr ((Fintype.equivFin {j // C j = true})
      ⟨i,by cases hci : C i <;> simp_all⟩)
  left_inv i := by
    cases i with
    | inl i => simp [((Fintype.equivFin {j // C j = false}).symm i).property]
    | inr i =>
        have hi := ((Fintype.equivFin {j // C j = true}).symm i).property
        simp [hi]
  right_inv i := by
    by_cases h : C i = false <;> simp [h]

def cutSignature (ps : List (ProductFactor n)) (C : Fin n → Bool) (b : Bool) :
    Signature AlgebraicComplex (Fintype.card {i // C i = b}) :=
  fun y => cutPiece ps C b (fun i => y ((Fintype.equivFin {j // C j = b}) i))

def cutSplit (c : AlgebraicComplex) (hc : c ≠ 0)
    (ps : List (ProductFactor n)) (C : Fin n → Bool)
    (closed : CutClosed ps C) (h0 : ∃ i, C i = false) (h1 : ∃ i, C i = true) :
    ProperSplit (⟨n,productFormula c ps⟩ : AnySignature AlgebraicComplex)
      ⟨Fintype.card {i // C i = false},cutSignature ps C false⟩
      ⟨Fintype.card {i // C i = true},cutSignature ps C true⟩ where
  left_pos := by
    change 0 < Fintype.card {i // C i = false}
    apply Fintype.card_pos_iff.mpr
    obtain ⟨i,hi⟩ := h0
    exact ⟨⟨i,hi⟩⟩
  right_pos := by
    change 0 < Fintype.card {i // C i = true}
    apply Fintype.card_pos_iff.mpr
    obtain ⟨i,hi⟩ := h1
    exact ⟨⟨i,hi⟩⟩
  ports := cutPorts C
  scale := Units.mk0 c hc
  equation := by
    funext x
    simp only [cutSignature,cutPorts,Equiv.coe_fn_mk,Equiv.symm_apply_apply,
      Units.val_mk0]
    rw [cutPiece_restrict ps C closed false x,cutPiece_restrict ps C closed true x,
      cutProduct_mul]
    rfl

/-- This is an all-arity statement about the unrestricted ProductFactor list.
Repeated constraints, zero unary entries and arbitrary component sizes remain
allowed. The two factors retain precisely their disjoint original ports. -/
theorem product_components (f : Signature AlgebraicComplex n) (positive : 0 < n)
    (nonzero : f ≠ 0) (product : Product f) :
    (∃ s : Fin n → Bool, ∀ x, f x ≠ 0 → x = s ∨ x = fun i => !(s i)) ∨
      ∃ a b : AnySignature AlgebraicComplex, Nonempty (ProperSplit ⟨n,f⟩ a b) := by
  classical
  rcases product with zero | ⟨c,hc,ps,equation⟩
  · exact False.elim (nonzero zero)
  let root : Fin n := ⟨0,positive⟩
  by_cases connected : ∀ i, FactorConnected ps root i
  · left
    obtain ⟨s,hs⟩ : ∃ s, f s ≠ 0 := by
      by_contra none
      push_neg at none
      exact nonzero (funext none)
    refine ⟨s,fun x hx => ?_⟩
    rw [equation] at hs hx
    exact connected_support_pair c ps root connected s x hs hx
  · right
    obtain ⟨j,hj⟩ := not_forall.mp connected
    let C := componentCut ps root
    have h0 : ∃ i, C i = false := ⟨j,by simp [C,componentCut,hj]⟩
    have h1 : ∃ i, C i = true := ⟨root,componentCut_root ps root⟩
    rw [equation]
    exact ⟨_,_,⟨cutSplit c hc ps C (componentCut_closed ps root) h0 h1⟩⟩

/-- A prime Product signature may be a generalized equality of any arity.
This conclusion deliberately retains the complementary pair alternative. -/
theorem prime_product_support_pair (f : Signature AlgebraicComplex n)
    (positive : 0 < n) (prime : Prime (⟨n,f⟩ : AnySignature AlgebraicComplex))
    (product : Product f) :
    ∃ s : Fin n → Bool, ∀ x, f x ≠ 0 → x = s ∨ x = fun i => !(s i) :=
  (product_components f positive prime.1 product).resolve_right prime.2

/-- The same structural conclusion holds for the actual original-field
prime after its faithful field embedding; no ambient primality is assumed. -/
theorem embedded_prime_product_support_pair {K : Type*} [Field K]
    (φ : K →+* AlgebraicComplex) (f : Signature K n) (positive : 0 < n)
    (prime : Prime (⟨n,f⟩ : AnySignature K)) (product : Product (fun x => φ (f x))) :
    ∃ s : Fin n → Bool, ∀ x, f x ≠ 0 → x = s ∨ x = fun i => !(s i) := by
  have mapped := (prime_mapSignature_iff φ (⟨n,f⟩ : AnySignature K)).mpr prime
  obtain ⟨s,hs⟩ := prime_product_support_pair (fun x => φ (f x)) positive mapped product
  exact ⟨s,fun x hx => hs x ((map_ne_zero φ).mpr hx)⟩

/-- Singleton support gives a real two-block factorization across any
positive partition, regardless of whether its factors are physically exposed. -/
def singletonSplit {K : Type*} [Field K] {u v : ℕ}
    (f : Signature K n) (s : Fin n → Bool)
    (support : ∀ x, f x ≠ 0 → x = s)
    (ports : (Fin u ⊕ Fin v) ≃ Fin n) (hu : 0 < u) (hv : 0 < v) :
    ProperSplit (⟨n,f⟩ : AnySignature K)
      ⟨u,fun x => if x = (fun i => s (ports (.inl i))) then f s else 0⟩
      ⟨v,fun y => if y = (fun i => s (ports (.inr i))) then 1 else 0⟩ where
  left_pos := hu
  right_pos := hv
  ports := ports
  scale := 1
  equation := by
    classical
    funext x
    have together :
        ((fun i => x (ports (.inl i))) = (fun i => s (ports (.inl i))) ∧
         (fun i => x (ports (.inr i))) = (fun i => s (ports (.inr i)))) ↔ x = s := by
      constructor
      · rintro ⟨left,right⟩
        funext i
        obtain ⟨j,rfl⟩ := ports.surjective i
        cases j with
        | inl j => exact congrFun left j
        | inr j => exact congrFun right j
      · intro equal
        subst x
        exact ⟨rfl,rfl⟩
    by_cases equal : x = s
    · subst x
      simp
    · have zero : f x = 0 := by
        by_contra live
        exact equal (support x live)
      have different := mt together.mp equal
      rcases not_and_or.mp different with left | right
      · simp [zero,left]
      · simp [zero,right]

theorem prime_not_singleton {K : Type*} [Field K] (f : Signature K n)
    (large : 2 ≤ n) (prime : Prime (⟨n,f⟩ : AnySignature K))
    (s : Fin n → Bool) : ¬ ∀ x, f x ≠ 0 → x = s := by
  intro support
  have arity : 1 + (n-1) = n := by omega
  let ports : (Fin 1 ⊕ Fin (n-1)) ≃ Fin n :=
    (finSumFinEquiv : (Fin 1 ⊕ Fin (n-1)) ≃ Fin (1+(n-1))).trans (finCongr arity)
  exact prime.2 ⟨_,_,⟨singletonSplit f s support ports (by omega) (by omega)⟩⟩

/-- At arity at least two the complementary coefficients are both nonzero.
Singleton support is excluded by a literal proper split, not by an assumed
nondegeneracy convention on Product formulas. -/
theorem prime_product_exact_support (f : Signature AlgebraicComplex n)
    (large : 2 ≤ n) (prime : Prime (⟨n,f⟩ : AnySignature AlgebraicComplex))
    (product : Product f) :
    ∃ s : Fin n → Bool, ∀ x, f x ≠ 0 ↔ x = s ∨ x = fun i => !(s i) := by
  classical
  obtain ⟨s,support⟩ := prime_product_support_pair f (by omega) prime product
  have first : f s ≠ 0 := by
    intro zero
    apply prime_not_singleton f large prime (fun i => !(s i))
    intro x live
    exact (support x live).resolve_left (fun same => live (same ▸ zero))
  have second : f (fun i => !(s i)) ≠ 0 := by
    intro zero
    apply prime_not_singleton f large prime s
    intro x live
    exact (support x live).resolve_right (fun same => live (same ▸ zero))
  exact ⟨s,fun x => ⟨support x,fun h => h.elim (fun same => same ▸ first)
    (fun same => same ▸ second)⟩⟩

theorem prime_product_complement (f : Signature AlgebraicComplex n)
    (large : 2 ≤ n) (prime : Prime (⟨n,f⟩ : AnySignature AlgebraicComplex))
    (product : Product f) (x : Fin n → Bool) :
    f (fun i => !(x i)) ≠ 0 ↔ f x ≠ 0 := by
  obtain ⟨s,support⟩ := prime_product_exact_support f large prime product
  rw [support,support]
  constructor
  · rintro (equal | equal)
    · right
      funext i
      have hi := congrFun equal i
      cases hxi : x i <;> cases hsi : s i <;> simp_all
    · left
      funext i
      have hi := congrFun equal i
      cases hxi : x i <;> cases hsi : s i <;> simp_all
  · rintro (rfl | rfl)
    · exact .inr rfl
    · exact .inl (by funext i; simp)

def signedStarFactor (root : Fin n) (s : Fin n → Bool) (i : Fin n) : ProductFactor n :=
  if s root = s i then .equality root i else .disequality root i

theorem signedStarFactor_eval (root : Fin n) (s x : Fin n → Bool) (i : Fin n) :
    (signedStarFactor root s i).eval x =
      if (x root ^^ s root) = (x i ^^ s i) then 1 else 0 := by
  cases hsr : s root <;> cases hsi : s i <;> cases hxr : x root <;> cases hxi : x i <;>
    simp [signedStarFactor,hsr,hsi,hxr,hxi,ProductFactor.eval,Signature.equality,Signature.disequality]

theorem common_relative_iff (root : Fin n) (s x : Fin n → Bool) :
    (∀ i, (x root ^^ s root) = (x i ^^ s i)) ↔
      x = s ∨ x = fun i => !(s i) := by
  constructor
  · intro common
    by_cases same : x root = s root
    · left
      funext i
      have hi := common i
      have zero : (x root ^^ s root) = false := by simp [same]
      have zero' := hi.symm.trans zero
      cases hxi : x i <;> cases hsi : s i <;> simp_all
    · right
      funext i
      have hi := common i
      cases hxr : x root <;> cases hsr : s root <;>
        cases hxi : x i <;> cases hsi : s i <;> simp_all
  · rintro (rfl | rfl) i
    · simp
    · change ((!s root) ^^ s root) = ((!s i) ^^ s i)
      cases s root <;> cases s i <;> decide

theorem signed_star_product (root : Fin n) (s : Fin n → Bool) :
    Product (fun x : Fin n → Bool =>
      if x = s ∨ x = (fun i => !(s i)) then 1 else 0) := by
  classical
  have products (indices : Finset (Fin n)) :
      Product (fun x : Fin n → Bool => ∏ i ∈ indices, (signedStarFactor root s i).eval x) := by
    induction indices using Finset.induction_on with
    | empty => simpa using product_constant n 1
    | @insert i indices hi ih =>
        simpa only [Finset.prod_insert hi] using (product_factor (signedStarFactor root s i)).mul ih
  convert products Finset.univ using 1
  funext x
  simp only [signedStarFactor_eval]
  by_cases common : ∀ i, (x root ^^ s root) = (x i ^^ s i)
  · rw [if_pos ((common_relative_iff root s x).mp common)]
    symm
    apply Finset.prod_eq_one
    intro i _
    exact if_pos (common i)
  · rw [if_neg (mt (common_relative_iff root s x).mpr common)]
    obtain ⟨i,hi⟩ := not_forall.mp common
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

/-- A complementary support pair has a literal signed equality-star Product
formula, with exactly its two original coefficients and no division. -/
theorem product_of_support_pair (f : Signature AlgebraicComplex n) (root : Fin n)
    (s : Fin n → Bool)
    (support : ∀ x, f x ≠ 0 → x = s ∨ x = fun i => !(s i)) : Product f := by
  classical
  have result := (product_unary root (fun b => if b = s root then f s
    else f (fun i => !(s i)))).mul (signed_star_product root s)
  convert result using 1
  funext x
  by_cases first : x = s
  · subst x
    simp
  · by_cases second : x = (fun i => !(s i))
    · subst x
      have bitDifferent : !(s root) ≠ s root := by cases s root <;> decide
      simp [bitDifferent]
    · have zero : f x = 0 := by
        by_contra live
        exact (support x live).elim first second
      simp [zero,first,second]

theorem prime_product_iff_support_pair (f : Signature AlgebraicComplex n)
    (positive : 0 < n) (prime : Prime (⟨n,f⟩ : AnySignature AlgebraicComplex)) :
    Product f ↔ ∃ s : Fin n → Bool,
      ∀ x, f x ≠ 0 → x = s ∨ x = fun i => !(s i) := by
  constructor
  · exact prime_product_support_pair f positive prime
  · rintro ⟨s,support⟩
    exact product_of_support_pair f ⟨0,positive⟩ s support

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionProductAncestorSupport
end
