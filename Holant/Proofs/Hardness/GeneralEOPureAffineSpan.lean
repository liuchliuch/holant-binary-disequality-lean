import Holant.Proofs.Hardness.GeneralEODEQProducerSupportBasic
import Holant.Proofs.Hardness.GeneralEONegativeClosedSupport

/-! The finite affine span of a pure support. Averaging its signed charge
produces a forced favorable coordinate whenever the span is not central. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPureAffineSpan
open Holant Holant.Tractable GeneralEODEQProducerSupportBasic
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

def signBit : EOSign → Bool | .positive => true | .negative => false

theorem signed_spin (sign : EOSign) (b : Bool) :
    sign.value * spin b = if b = signBit sign then 1 else -1 := by
  cases sign <;> cases b <;> norm_num [EOSign.value, spin, signBit]

def Span (f : Signature AlgebraicComplex n) (x : Fin n → Bool) : Prop :=
  ∃ xs : List (Fin n → Bool), Odd xs.length ∧ (∀ y ∈ xs, f y ≠ 0) ∧ xorList xs = x

theorem support_span {f : Signature AlgebraicComplex n} {x : Fin n → Bool}
    (hx : f x ≠ 0) : Span f x := by
  refine ⟨[x],by norm_num,by simpa,?_⟩
  funext i
  simp [xorList]

theorem xorList_append (xs ys : List (Fin n → Bool)) :
    xorList (xs ++ ys) = fun i => Bool.xor (xorList xs i) (xorList ys i) := by
  induction xs with
  | nil => simp [xorList]
  | cons x xs ih =>
    funext i
    simp only [List.cons_append, xorList_cons, ih]
    cases x i <;> cases xorList xs i <;> cases xorList ys i <;> rfl

theorem span_closed {f : Signature AlgebraicComplex n} {a b c : Fin n → Bool}
    (ha : Span f a) (hb : Span f b) (hc : Span f c) : Span f (tripleXor a b c) := by
  obtain ⟨xs,hxo,hxs,rfl⟩ := ha
  obtain ⟨ys,hyo,hys,rfl⟩ := hb
  obtain ⟨zs,hzo,hzs,rfl⟩ := hc
  refine ⟨(xs ++ ys) ++ zs,?_,?_,?_⟩
  · simp only [List.length_append]
    rw [Nat.odd_iff] at hxo hyo hzo ⊢
    omega
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · rcases List.mem_append.mp hx with hx | hx
      · exact hxs x hx
      · exact hys x hx
    · exact hzs x hx
  · rw [xorList_append, xorList_append]
    rfl

def points (f : Signature AlgebraicComplex n) : Finset (Fin n → Bool) :=
  by classical exact Finset.univ.filter (Span f)

@[simp] theorem mem_points (f : Signature AlgebraicComplex n) (x : Fin n → Bool) :
    x ∈ points f ↔ Span f x := by classical simp [points]

abbrev Point (f : Signature AlgebraicComplex n) := {x // x ∈ points f}

def translate (f : Signature AlgebraicComplex n) (a b : Point f) : Point f ≃ Point f where
  toFun x := ⟨tripleXor a.val b.val x.val, (mem_points f _).mpr
    (span_closed ((mem_points f _).mp a.property) ((mem_points f _).mp b.property)
      ((mem_points f _).mp x.property))⟩
  invFun x := ⟨tripleXor a.val b.val x.val, (mem_points f _).mpr
    (span_closed ((mem_points f _).mp a.property) ((mem_points f _).mp b.property)
      ((mem_points f _).mp x.property))⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    dsimp [tripleXor]
    cases a.val i <;> cases b.val i <;> cases x.val i <;> rfl
  right_inv x := by
    apply Subtype.ext
    funext i
    dsimp [tripleXor]
    cases a.val i <;> cases b.val i <;> cases x.val i <;> rfl

/-- A varying coordinate is balanced over the entire affine span. -/
theorem coordinate_sum_zero (f : Signature AlgebraicComplex n) (a b : Point f)
    (i : Fin n) (hi : a.val i ≠ b.val i) :
    (∑ x : Point f, spin (x.val i)) = 0 := by
  have h := (translate f a b).sum_comp (fun x => spin (x.val i))
  have ht (x : Point f) : spin ((translate f a b x).val i) = -spin (x.val i) := by
    change spin (Bool.xor (Bool.xor (a.val i) (b.val i)) (x.val i)) = _
    cases ha : a.val i <;> cases hb : b.val i <;> cases x.val i <;> simp_all [spin]
  simp only [ht, Finset.sum_neg_distrib] at h
  omega

/-- Without a favorable fixed column, the average signed charge is nonpositive. -/
theorem total_nonpos (f : Signature AlgebraicComplex n) (hn : f ≠ 0) (sign : EOSign)
    (hf : ¬∃ i, ∀ x, Span f x → x i = signBit sign) :
    (∑ x : Point f, sign.value * charge x.val) ≤ 0 := by
  classical
  obtain ⟨base,hbase⟩ := Function.ne_iff.mp hn
  let b : Point f := ⟨base,(mem_points f _).mpr (support_span hbase)⟩
  simp only [charge_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_nonpos
  intro i _
  by_cases hv : ∃ a : Point f, a.val i ≠ b.val i
  · obtain ⟨a,ha⟩ := hv
    rw [← Finset.mul_sum, coordinate_sum_zero f a b i ha, mul_zero]
  · have heq : ∀ x : Point f, x.val i = b.val i := by simpa using hv
    have hb : b.val i ≠ signBit sign := by
      intro hh
      apply hf
      refine ⟨i,?_⟩
      intro x hx
      exact (heq ⟨x,(mem_points f x).mpr hx⟩).trans hh
    apply Finset.sum_nonpos
    intro x _
    rw [heq x, signed_spin, if_neg hb]
    norm_num

/-- The finite averaging lemma, with the sign fixed throughout. -/
theorem central_or_fixed (f : Signature AlgebraicComplex n) (hn : f ≠ 0)
    (sign : EOSign) (hp : Pure sign f) :
    (∀ x, Span f x → charge x = 0) ∨
      ∃ i, ∀ x, f x ≠ 0 → x i = signBit sign := by
  classical
  by_cases hcentral : ∀ x, Span f x → charge x = 0
  · exact Or.inl hcentral
  · right
    have hnonneg (x : Point f) : 0 ≤ sign.value * charge x.val := by
      obtain ⟨xs,ho,hs,hx⟩ := (mem_points f _).mp x.property
      rw [←hx]
      exact hp xs ho hs
    obtain ⟨y,hy,hyn⟩ : ∃ y, Span f y ∧ charge y ≠ 0 := by
      push_neg at hcentral
      exact hcentral
    have hpos : 0 < ∑ x : Point f, sign.value * charge x.val := by
      apply Finset.sum_pos' (fun x _ => hnonneg x)
      refine ⟨⟨y,(mem_points f _).mpr hy⟩,Finset.mem_univ _,?_⟩
      have hh := hnonneg ⟨y,(mem_points f _).mpr hy⟩
      cases sign <;> simp only [EOSign.value] at hh ⊢ <;> omega
    have hfixed : ∃ i, ∀ x, Span f x → x i = signBit sign := by
      by_contra hf
      have hn := total_nonpos f hn sign hf
      omega
    obtain ⟨i,hi⟩ := hfixed
    exact ⟨i,fun x hx => hi x (support_span hx)⟩

/-- With the original common-sign support condition, a central affine span
is actual closed support, not an assumed covering pairing. -/
theorem closed_of_span_central (f : Signature AlgebraicComplex n) (sign : EOSign)
    (hs : EONegativeWitness.Supports sign ⟨n,f⟩)
    (hc : ∀ x, Span f x → charge x = 0) : GeneralEONegativeClosedSupport.Closed f := by
  intro a b c ha hb hb'
  have hzero := hc _ (span_closed (support_span ha) (support_span hb) (support_span hb'))
  have h := hs a b c ha hb hb'
  rw [hzero,mul_zero] at h
  exact h.resolve_right (by omega)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPureAffineSpan
