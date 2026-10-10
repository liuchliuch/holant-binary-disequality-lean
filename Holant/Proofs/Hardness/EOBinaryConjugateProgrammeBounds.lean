import Holant.Proofs.Hardness.EOBinaryConjugateProgrammeState
import Holant.Proofs.Hardness.ThreeModeFilterBounds

/-! Polynomial arithmetic-height invariants for the concrete collision-aware
controller. Current filter values grow with the number of scanned roots; the
fraction accumulator grows additively by one whole term budget per round. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryConjugateProgrammeBounds
open Holant.OneHot
open EOBinaryConjugateProgrammeState
variable {L A : Type} [Field L] [Algebra ℚ L]
variable (base : A→L) (unit minus : A) (hunit : base unit=1) (hminus : base minus = -1)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false

def scanned (s : State L) : ℕ := s.roots.length-s.remaining.length
def filterBudget (R : ℕ) (s : State L) : ℕ := scanned s*(R+2)
def termBudget (R U : ℕ) (s : State L) : ℕ := U+R+(s.roots.length+1)*(R+3)+4

structure Bounded (R U V : ℕ) (s : State L) : Prop where
  roots : ∀p∈s.roots,ArithmeticSize.Bound base R p.1 ∧ ArithmeticSize.Bound base R p.2
  pending : ∀p∈s.pending,ArithmeticSize.Bound base R p.1 ∧ ArithmeticSize.Bound base R p.2
  remaining : ∀p∈s.remaining,ArithmeticSize.Bound base R p.1 ∧ ArithmeticSize.Bound base R p.2
  pending_length : s.pending.length≤s.roots.length
  remaining_length : s.remaining.length≤s.roots.length
  moments : ∀x∈s.moments,ArithmeticSize.Bound base U x
  values : ∀x∈s.values,ArithmeticSize.Bound base (U+filterBudget R s) x
  values_length : s.values.length≤s.moments.length
  denominator : ArithmeticSize.Bound base (R+filterBudget R s) s.denominator
  multiplicity : ArithmeticSize.Bound base (scanned s+1) s.multiplicity
  numerator : ArithmeticSize.Bound base V s.numerator
  divisor : ArithmeticSize.Bound base V s.divisor

include unit hunit in
theorem pair_getD (xs : List (L×L)) (k R : ℕ)
    (h : ∀p∈xs,ArithmeticSize.Bound base R p.1 ∧ ArithmeticSize.Bound base R p.2) :
    ArithmeticSize.Bound base R (xs.getD k (0,0)).1 ∧
    ArithmeticSize.Bound base R (xs.getD k (0,0)).2 := by
  by_cases hk : k<xs.length
  · rw [List.getD_eq_getElem _ _ hk]
    exact h _ (List.getElem_mem hk)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact ⟨ArithmeticSize.Bound.zero unit R,ArithmeticSize.Bound.zero unit R⟩

include unit hunit in
theorem Bounded.mono {R U V V' : ℕ} {s : State L} (h : Bounded base R U V s) (hv : V≤V') :
    Bounded base R U V' s :=
  {h with numerator:=h.numerator.mono unit hunit hv,divisor:=h.divisor.mono unit hunit hv}

include unit hunit in
theorem initial_bounded {R U : ℕ} (rs : List (L×L)) (ys : List L)
    (hr : ∀p∈rs,ArithmeticSize.Bound base R p.1 ∧ ArithmeticSize.Bound base R p.2)
    (hy : ∀y∈ys,ArithmeticSize.Bound base U y) :
    Bounded base R U 0 (initial rs ys) := by
  have hd := (pair_getD base unit hunit rs 0 R hr).1
  refine ⟨hr,hr,hr,le_rfl,le_rfl,hy,?_,le_rfl,?_,?_,?_,?_⟩
  · simpa [filterBudget,scanned,initial] using hy
  · simpa [filterBudget,scanned,initial] using hd
  · exact ArithmeticSize.Bound.zero unit _
  · exact ArithmeticSize.Bound.zero unit _
  · exact ArithmeticSize.Bound.one

include unit minus hunit hminus in
theorem bounded_scanDifferent {R U V : ℕ} {s : State L} (h : Bounded base R U V s)
    (hr : s.remaining≠[]) : Bounded base R U V (scanDifferent s) := by
  have hl : 0<s.remaining.length := List.length_pos_iff.mpr hr
  have hs : scanned (scanDifferent s)=scanned s+1 := by
    simp only [scanned,scanDifferent,List.length_tail]
    have hrl:=h.remaining_length
    omega
  have hb : filterBudget R (scanDifferent s)=filterBudget R s+R+2 := by
    simp only [filterBudget,hs]
    ring
  have hroot := (pair_getD base unit hunit s.remaining 0 R h.remaining).1
  have hdesired := (pair_getD base unit hunit s.pending 0 R h.pending).1
  refine ⟨h.roots,h.pending,?_,h.pending_length,?_,h.moments,?_,?_,?_,?_,h.numerator,h.divisor⟩
  · intro p hp
    exact h.remaining p (List.mem_of_mem_tail hp)
  · exact by
      change s.remaining.tail.length≤s.roots.length
      rw [List.length_tail]
      exact (Nat.sub_le _ _).trans h.remaining_length
  · have hv := ThreeModeFilter.difference_bound base unit minus hunit hminus hroot h.values
    change ∀x∈ThreeModeFilter.difference (root s) s.values,
      ArithmeticSize.Bound base (U+filterBudget R (scanDifferent s)) x
    rw [hb]
    simpa only [root,Nat.add_assoc] using hv
  · exact (by
      change (ThreeModeFilter.difference _ _).length≤_
      rw [ThreeModeFilter.difference_length]
      exact (Nat.sub_le _ _).trans h.values_length)
  · have hd := h.denominator.mul (ThreeModeFilter.sub_bound base unit minus hunit hminus hdesired hroot)
    change ArithmeticSize.Bound base (R+filterBudget R (scanDifferent s))
      (s.denominator*((desired s).1-root s))
    rw [hb]
    simpa only [root,desired,Nat.add_assoc] using hd
  · exact h.multiplicity.mono unit hunit (by rw [hs]; omega)

include unit hunit in
theorem bounded_scanEqual {R U V : ℕ} {s : State L} (h : Bounded base R U V s)
    (hr : s.remaining≠[]) : Bounded base R U V (scanEqual s) := by
  have hl : 0<s.remaining.length := List.length_pos_iff.mpr hr
  have hs : scanned (scanEqual s)=scanned s+1 := by
    simp only [scanned,scanEqual,List.length_tail]
    have hrl:=h.remaining_length
    omega
  have hb : filterBudget R s≤filterBudget R (scanEqual s) := by
    simp only [filterBudget,hs]
    exact Nat.mul_le_mul_right (R+2) (Nat.le_add_right _ 1)
  refine ⟨h.roots,h.pending,?_,h.pending_length,?_,h.moments,?_,h.values_length,?_,?_,h.numerator,h.divisor⟩
  · intro p hp
    exact h.remaining p (List.mem_of_mem_tail hp)
  · exact by
      change s.remaining.tail.length≤s.roots.length
      rw [List.length_tail]
      exact (Nat.sub_le _ _).trans h.remaining_length
  · exact fun x hx=>(h.values x hx).mono unit hunit (by omega)
  · exact h.denominator.mono unit hunit (by omega)
  · have ho : ArithmeticSize.Bound base (scanned s+1) (1 : L) :=
      ArithmeticSize.Bound.one.mono unit hunit (Nat.zero_le _)
    change ArithmeticSize.Bound base (scanned (scanEqual s)+1) (s.multiplicity+1)
    rw [hs]
    exact h.multiplicity.add unit hunit ho

include unit hunit in
theorem bounded_advance {R U V : ℕ} {s : State L} (h : Bounded base R U V s) :
    Bounded base R U (V+termBudget R U s) (advance s) := by
  have hs : scanned (advance s)=0 := by simp [scanned,advance]
  have hb : filterBudget R (advance s)=0 := by simp [filterBudget,hs]
  have hn := (pair_getD base unit hunit s.pending 1 R h.pending).1
  have hz := (pair_getD base unit hunit s.pending 0 R h.pending).2
  have hy := ThreeModeFilter.getD_bound base unit hunit s.values (U+filterBudget R s) 0 h.values
  have hd := h.denominator.mul h.multiplicity
  have ht := hz.mul hy
  have hm : scanned s≤s.roots.length := Nat.sub_le _ _
  have bd : R+filterBudget R s+(scanned s+1)≤termBudget R U s-1 := by
    apply Nat.le_sub_of_add_le
    unfold filterBudget termBudget
    nlinarith [Nat.mul_le_mul_right (R+2) hm]
  have bt : R+(U+filterBudget R s)≤termBudget R U s-1 := by
    apply Nat.le_sub_of_add_le
    unfold filterBudget termBudget
    nlinarith [Nat.mul_le_mul_right (R+2) hm]
  have hc : 1≤termBudget R U s := by unfold termBudget; omega
  refine ⟨h.roots,?_,h.roots,?_,le_rfl,h.moments,?_,le_rfl,?_,?_,?_,?_⟩
  · intro p hp
    exact h.pending p (List.mem_of_mem_tail hp)
  · exact by
      change s.pending.tail.length≤s.roots.length
      rw [List.length_tail]
      exact (Nat.sub_le _ _).trans h.pending_length
  · change ∀x∈s.moments,ArithmeticSize.Bound base (U+filterBudget R (advance s)) x
    simpa only [hb,Nat.add_zero] using h.moments
  · change ArithmeticSize.Bound base (R+filterBudget R (advance s)) (nextDesired s).1
    simpa only [hb,Nat.add_zero,nextDesired] using hn
  · exact ArithmeticSize.Bound.zero unit _
  · have h₁ := (h.numerator.mul hd).mono unit hunit
      (show V+(R+filterBudget R s+(scanned s+1))≤V+(termBudget R U s-1) by omega)
    have h₂ := (ht.mul h.divisor).mono unit hunit
      (show R+(U+filterBudget R s)+V≤V+(termBudget R U s-1) by omega)
    have hh := h₁.add unit hunit h₂
    have he : V+(termBudget R U s-1)+1=V+termBudget R U s := by omega
    simpa only [advance,desired,he] using hh
  · exact (h.divisor.mul hd).mono unit hunit (by omega)

include unit minus hunit hminus in
theorem bounded_step {R U V : ℕ} {s : State L} (h : Bounded base R U V s) :
    Bounded base R U (V+termBudget R U s) (step s) := by
  classical
  unfold step
  split_ifs with hp hr he
  · exact Bounded.mono base unit hunit h (Nat.le_add_right _ _)
  · exact bounded_advance base unit hunit h
  · exact Bounded.mono base unit hunit (bounded_scanEqual base unit hunit h hr) (Nat.le_add_right _ _)
  · exact Bounded.mono base unit hunit (bounded_scanDifferent base unit minus hunit hminus h hr) (Nat.le_add_right _ _)

@[simp] theorem step_roots (s : State L) : (step s).roots=s.roots := by
  classical
  simp only [step]
  split_ifs <;> rfl
@[simp] theorem step_moments (s : State L) : (step s).moments=s.moments := by
  classical
  simp only [step]
  split_ifs <;> rfl
@[simp] theorem step_fuel (s : State L) : (step s).fuel=s.fuel := by
  classical
  simp only [step]
  split_ifs <;> rfl

@[simp] theorem iterate_roots (s : State L) (i : ℕ) : ((step^[i]) s).roots=s.roots := by
  induction i with
  | zero => rfl
  | succ i ih => rw [Function.iterate_succ_apply',step_roots,ih]
@[simp] theorem iterate_moments (s : State L) (i : ℕ) : ((step^[i]) s).moments=s.moments := by
  induction i with
  | zero => rfl
  | succ i ih => rw [Function.iterate_succ_apply',step_moments,ih]
@[simp] theorem iterate_fuel (s : State L) (i : ℕ) : ((step^[i]) s).fuel=s.fuel := by
  induction i with
  | zero => rfl
  | succ i ih => rw [Function.iterate_succ_apply',step_fuel,ih]

include unit minus hunit hminus in
theorem bounded_iterate {R U V : ℕ} {s : State L} (h : Bounded base R U V s) (i : ℕ) :
    Bounded base R U (V+i*termBudget R U s) ((step^[i]) s) := by
  induction i with
  | zero => simpa using h
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    have ht := bounded_step base unit minus hunit hminus ih
    have he : termBudget R U ((step^[i]) s)=termBudget R U s := by simp [termBudget]
    have he' : V+i*termBudget R U s+termBudget R U s=V+(i+1)*termBudget R U s := by ring
    simpa only [he,he'] using ht

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryConjugateProgrammeBounds
