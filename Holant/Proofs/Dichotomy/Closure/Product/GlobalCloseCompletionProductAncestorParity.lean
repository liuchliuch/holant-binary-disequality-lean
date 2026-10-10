import Holant.Proofs.Dichotomy.Closure.Product.GlobalCloseCompletionProductAncestorSupport
import Holant.Proofs.Closure.ClosureCompatibleAlignmentParity

/-! Support parity for generalized Product components. The parity conclusion
uses even arity of the actual prime components, not binary matching. It is
preserved by exact ordered splits, faithful embedding and nonzero scaling. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionProductAncestorParity
open Holant Holant.Tractable
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open GlobalCloseCompletionProductAncestorSupport
open ClosureSixPort (Word bit parity)
open ClosureCompatibleAlignment
open scoped BigOperators

def PureParity {K : Type*} [Zero K] {n : ℕ} (f : Signature K n) : Prop :=
  ∀ x y, f x ≠ 0 → f y ≠ 0 → parity x = parity y

theorem complement_parity {n : ℕ} (even : Even n) (x : Word n) :
    parity (fun i => !(x i)) = parity x := by
  have sum : parity (fun i => !(x i)) + parity x = (n : ZMod 2) := by
    unfold parity
    rw [←Finset.sum_add_distrib]
    calc
      (∑ i, (bit (!(x i)) + bit (x i))) = ∑ _ : Fin n, (1 : ZMod 2) := by
        apply Finset.sum_congr rfl
        intro i _
        cases x i <;> decide
      _ = (n : ZMod 2) := by simp
  have zero : (n : ZMod 2) = 0 := by
    obtain ⟨k,rfl⟩ := even
    simp only [Nat.cast_add]
    calc
      (k : ZMod 2) + k = (2 : ZMod 2) * k := by ring
      _ = 0 := by rw [show (2 : ZMod 2) = 0 by decide,zero_mul]
  have self : parity x + parity x = 0 := by
    calc
      parity x + parity x = (2 : ZMod 2) * parity x := by ring
      _ = 0 := by rw [show (2 : ZMod 2) = 0 by decide,zero_mul]
  exact add_right_cancel ((sum.trans zero).trans self.symm)

theorem prime_product_pureParity {n : ℕ} (f : Signature AlgebraicComplex n)
    (positive : 0 < n) (even : Even n)
    (prime : Prime (⟨n,f⟩ : AnySignature AlgebraicComplex)) (product : Product f) :
    PureParity f := by
  obtain ⟨s,support⟩ := prime_product_support_pair f positive prime product
  intro x y hx hy
  rcases support x hx with rfl | rfl <;>
    rcases support y hy with rfl | rfl <;> simp [complement_parity even]

theorem pureParity_map_iff {K L : Type*} [Field K] [Field L]
    (φ : K →+* L) {n : ℕ} (f : Signature K n) :
    PureParity (fun x => φ (f x)) ↔ PureParity f := by
  constructor
  · intro h x y hx hy
    exact h x y ((map_ne_zero φ).mpr hx) ((map_ne_zero φ).mpr hy)
  · intro h x y hx hy
    exact h x y ((map_ne_zero φ).mp hx) ((map_ne_zero φ).mp hy)

theorem pureParity_scale {K : Type*} [Field K] {n : ℕ}
    (f : Signature K n) (h : PureParity f) (c : K) : PureParity (c • f) := by
  intro x y hx hy
  exact h x y (mul_ne_zero_iff.mp hx).2 (mul_ne_zero_iff.mp hy).2

theorem pureParity_unscale {K : Type*} [Field K] {n : ℕ}
    (f : Signature K n) (c : K) (hc : c ≠ 0) (h : PureParity (c • f)) : PureParity f := by
  intro x y hx hy
  exact h x y (mul_ne_zero hc hx) (mul_ne_zero hc hy)

theorem pureParity_zero {K : Type*} [Zero K] (n : ℕ) :
    PureParity (0 : Signature K n) := by
  intro x _ hx _
  exact False.elim (hx rfl)

theorem parity_split {k m n : ℕ} (ports : (Fin m ⊕ Fin n) ≃ Fin k) (x : Word k) :
    parity x = parity (fun i => x (ports (.inl i))) +
      parity (fun i => x (ports (.inr i))) := by
  unfold parity
  rw [←Equiv.sum_comp ports (fun i => bit (x i)),Fintype.sum_sum_type]

theorem pureParity_split {K : Type*} [Field K] {f a b : AnySignature K}
    (split : ProperSplit f a b) (left : PureParity a.2) (right : PureParity b.2) :
    PureParity f.2 := by
  intro x y hx hy
  rw [split.equation] at hx hy
  have hx' := mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hx).2
  have hy' := mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hy).2
  rw [parity_split split.ports x,parity_split split.ports y,
    left _ _ hx'.1 hy'.1,right _ _ hx'.2 hy'.2]

/-- The actual saved leaves may have any positive even arity. Their Product
support pairs give support parity of the whole original-field tree. -/
theorem factorTree_pureParity {K : Type*} [Field K]
    (φ : K →+* AlgebraicComplex) {f : AnySignature K} (tree : FactorTree f)
    (leaves : ∀ a ∈ tree.leaves,
      0 < a.1 ∧ Even a.1 ∧ Product (fun x => φ (a.2 x))) : PureParity f.2 := by
  induction tree with
  | leaf f prime =>
      have data := leaves f (by simp [FactorTree.leaves])
      apply (pureParity_map_iff φ f.2).mp
      exact prime_product_pureParity _ data.1 data.2.1
        ((prime_mapSignature_iff φ f).mpr prime) data.2.2
  | split split left right ihl ihr =>
      apply pureParity_split split
      · apply ihl
        intro a ha
        exact leaves a (Multiset.mem_add.mpr (Or.inl ha))
      · apply ihr
        intro a ha
        exact leaves a (Multiset.mem_add.mpr (Or.inr ha))

/-- Three actual root samples suffice to transport support parity through
both analytic slices, even when some sampled cards are zero. -/
theorem endpoint_same_parity {n m : ℕ} (range : 3 ≤ m) (f : Signature ℂ (n+2))
    (deck : ∀ e p t, t^m=1 → PureParity (phaseCardN f e p t))
    (e : Equiv.Perm (Fin (n+2))) (p a b : Bool) (x y : Word n)
    (hx : slicePairN f e p a x ≠ 0) (hy : slicePairN f e p b y ≠ 0) :
    parity x = parity y := by
  by_contra different
  have cross (t : ℂ) (ht : t^m=1) :
      phaseCardN f e p t x * phaseCardN f e p t y = 0 := by
    by_cases zero : phaseCardN f e p t x = 0
    · rw [zero,zero_mul]
    · have zero' : phaseCardN f e p t y = 0 := by
        by_contra live
        exact different (deck e p t ht x y zero live)
      rw [zero',mul_zero]
  rcases Holant.Projective.affine_product_zero_on_rootPolygon range
    (slicePairN f e p false x) (slicePairN f e p true x)
    (slicePairN f e p false y) (slicePairN f e p true y) cross with zero | zero
  · cases a
    · exact hx zero.1
    · exact hx zero.2
  · cases b
    · exact hy zero.1
    · exact hy zero.2

theorem same_deleted_parity {n m : ℕ} (range : 3 ≤ m) (f : Signature ℂ (n+2))
    (deck : ∀ e p t, t^m=1 → PureParity (phaseCardN f e p t))
    (e : Equiv.Perm (Fin (n+2))) (x y : Word (n+2))
    (hx : f x ≠ 0) (hy : f y ≠ 0)
    (same : (x (e 0) ^^ x (e 1)) = (y (e 0) ^^ y (e 1))) : parity x = parity y := by
  let p := x (e 0) ^^ x (e 1)
  have hleft : slicePairN f e p (x (e 0)) (residualPairN e x) ≠ 0 := by
    simpa only [slicePairN,p,fillPairN_reconstruct] using hx
  have hright : slicePairN f e p (y (e 0)) (residualPairN e y) ≠ 0 := by
    rw [show p = (y (e 0) ^^ y (e 1)) from same]
    simpa only [slicePairN,fillPairN_reconstruct] using hy
  have residual := endpoint_same_parity range f deck e p _ _ _ _ hleft hright
  rw [←fillPairN_reconstruct e x,←fillPairN_reconstruct e y,
    parity_fillPairN,parity_fillPairN,same,residual]

/-- Global parity is reconstructed from the genuine weaker parity property
of the cards. No root-matching presentation is used. -/
theorem pureParity_of_root_deck {n m : ℕ} (range : 3 ≤ m) (large : 3 ≤ n+2)
    (f : Signature ℂ (n+2))
    (deck : ∀ e p t, t^m=1 → PureParity (phaseCardN f e p t)) : PureParity f := by
  intro x y hx hy
  by_contra different
  have pairs (e : Equiv.Perm (Fin (n+2))) :
      (x (e 0) ^^ x (e 1)) ≠ (y (e 0) ^^ y (e 1)) :=
    fun equal => different (same_deleted_parity range f deck e x y hx hy equal)
  let third : Fin (n+2) := ⟨2,by omega⟩
  have zeroThird : (0 : Fin (n+2)) ≠ third := by
    intro equal
    have h := congrArg Fin.val equal
    change 0=2 at h
    omega
  have oneThird : (1 : Fin (n+2)) ≠ third := by
    intro equal
    have h := congrArg Fin.val equal
    have oneValue : (1 : Fin (n+2)).val=1 := by simp
    rw [oneValue] at h
    change 1=2 at h
    omega
  have impossible : ∀ a b c A B C : Bool,
      (a ^^ b) ≠ (A ^^ B) → (a ^^ c) ≠ (A ^^ C) →
      (b ^^ c) ≠ (B ^^ C) → False := by decide
  apply impossible (x 0) (x 1) (x third) (y 0) (y 1) (y third)
  · exact pairs (Equiv.refl _)
  · simpa only [Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne Fin.zero_ne_one zeroThird] using pairs (Equiv.swap 1 third)
  · simpa only [Equiv.trans_apply,Equiv.swap_apply_left,Equiv.swap_apply_right,
      Equiv.swap_apply_of_ne_of_ne (Ne.symm Fin.zero_ne_one) oneThird] using
      pairs ((Equiv.swap (0 : Fin (n+2)) 1).trans (Equiv.swap 0 third))

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (N : ClosureMarkedDihedral.NativeM
  (ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G) P.family torsion))

include N in
/-- Actual current keys and their original nonzero scalars supply the entire
root deck used by parity interpolation. No analytic deck is assumed. -/
theorem current_pureParity_of_rawDeck {n : ℕ} (f : Signature (OI.K G) (n+2))
    (large : 3 ≤ n+2)
    (deck : ∀ g ∈ rawDeck P.family torsion f, PureParity g) : PureParity f := by
  apply (pureParity_map_iff (ClosureSixPort.sourceComplex G) f).mp
  apply pureParity_of_root_deck N.range large
  intro order sector t ht
  let key := DeckContraction.orderedKey P.family torsion order
    (ClosureSixPort.cardIndex G P torsion N sector t ht).key
  have actual := (pureParity_map_iff (ClosureSixPort.sourceComplex G)
    (rawCard P.family torsion f key)).mpr (deck _ (Or.inr ⟨key,rfl⟩))
  change PureParity (Holant.LocalDrafts.MainChain.RingHomRealization.mapSignature
    (ClosureSixPort.sourceComplex G) (rawCard P.family torsion f key)) at actual
  rw [ClosureSixPort.ordered_card_raw_scalar G P torsion N f order sector t ht,
    ←phaseCardN_actual] at actual
  exact pureParity_unscale _ _
    (ClosureSixPort.cardScalar_nonzero G P torsion N sector t ht) actual

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionProductAncestorParity
end
