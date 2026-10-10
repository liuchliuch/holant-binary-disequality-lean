import Holant.Proofs.LinearProgramming.Support.MachineCombinators
import Holant.Proofs.LinearProgramming.Recovery.RationalExtraction.GlobalBounds

set_option autoImplicit false

/-! Kernel-checked recovery component. Three consecutive nonterminal blocks certify that two
jumps halve the positive endpoint potential. If a maximal jump lands past the
halving estimate, the next mediant lies inside the interval and terminates.
This connects linear ORIGINAL-BIT fuel to the actual status bytes, with no
recovered answer or optimization correctness supplied as a premise.
-/
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.RationalExtraction
open Holant.LocalDrafts.TraversalCompletion.RationalLP
open Holant.LocalDrafts.RemoteWork.RationalLP.Foundation
open Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators
namespace Termination
open Holant.Algebraic Holant.Complexity
def N (q : Query) (s : Neighbors) : ℤ := Fraction.lowerCross (lo q) s.1
def K (q : Query) (s : Neighbors) : ℤ := Fraction.upperCross (lo q) s.2
def potential (q : Query) (s : Neighbors) : ℤ := max (N q s) (K q s)

theorem positive (q : Query) (s : Neighbors) (hq : Valid q) (hs : Neighbors.Brackets q s) :
    0<N q s ∧ 0<K q s :=
  ⟨(Fraction.lowerCross_pos _ _ hs.1.1).mpr hs.2.1,
    (Fraction.upperCross_pos _ _ hs.1.2.1).mpr (lt_of_le_of_lt hq.1 hs.2.2)⟩
theorem pending_cases (q : Query) (s : Neighbors) (hd : done (Jump.step (q,s))=false) :
    (Fraction.value (Neighbors.middle s)<lo q ∧
      neighbors (Jump.step (q,s))=Neighbors.leftJump s (Jump.leftFactor q s)) ∨
    (hi q<Fraction.value (Neighbors.middle s) ∧
      neighbors (Jump.step (q,s))=Neighbors.rightJump s (Jump.rightFactor q s)) := by
  by_cases hc : cap q<s.1.2+s.2.2
  · simp [Jump.step,hc,done,miss] at hd
  · by_cases hl : Fraction.value (Neighbors.middle s)<lo q
    · exact Or.inl ⟨hl,by simp [Jump.step,hc,hl,neighbors,pending]⟩
    · by_cases hr : hi q<Fraction.value (Neighbors.middle s)
      · exact Or.inr ⟨hr,by simp [Jump.step,hc,hl,hr,neighbors,pending]⟩
      · simp [Jump.step,hc,hl,hr,done,hit] at hd

theorem three_pending_halves (q : Query) (s : Neighbors) (hq : Valid q) (hs : Neighbors.Brackets q s)
    (h1 : done (Jump.step (q,s))=false)
    (h2 : done (Jump.step (q,neighbors (Jump.step (q,s))))=false)
    (h3 : done (Jump.step (q,neighbors (Jump.step (q,neighbors (Jump.step (q,s))))))=false) :
    2*potential q (neighbors (Jump.step (q,neighbors (Jump.step (q,s)))))≤potential q s := by
  let s1 := neighbors (Jump.step (q,s))
  let s2 := neighbors (Jump.step (q,s1))
  have hs1 : Neighbors.Brackets q s1 := (Jump.step_safe q s hq hs).2.2 h1
  have hs2 : Neighbors.Brackets q s2 := (Jump.step_safe q s1 hq hs1).2.2 h2
  have hn0 := (positive q s hq hs).1
  have hk0 := (positive q s hq hs).2
  rcases pending_cases q s h1 with ⟨hl,e1⟩ | ⟨hr,e1⟩
  · have hp1 := Jump.left_progress q s hq hs hl
    have hm1 : lo q≤Fraction.value (Neighbors.middle s1) := by simpa only [s1,e1] using hp1.2.1
    rcases pending_cases q s1 h2 with ⟨hl2,e2⟩ | ⟨hr2,e2⟩
    · exact False.elim ((not_lt_of_ge hm1) hl2)
    · have hp2 := Jump.right_progress q s1 hq hs1 hr2
      have hm2 : Fraction.value (Neighbors.middle s2)≤hi q := by simpa only [s2,e2] using hp2.2.1
      have hleft2 : Fraction.value (Neighbors.middle s2)<lo q := by
        rcases pending_cases q s2 h3 with ⟨hl3,_⟩ | ⟨hr3,_⟩
        · exact hl3
        · exact False.elim ((not_lt_of_ge hm2) hr3)
      have hc2 : K q s2<N q s2 := (Neighbors.middle_lt_iff q s2 hs2.1).mp hleft2
      have hmax2 : potential q s2=N q s2 := max_eq_left hc2.le
      have hn1 : N q s1=N q s-(Jump.leftFactor q s:ℤ)*K q s := by
        dsimp only [s1]
        rw [e1]
        exact Jump.left_cross _ _ _
      have hk1 : K q s1=K q s := by dsimp only [s1]; rw [e1]; rfl
      have hn2 : N q s2=N q s1 := by dsimp only [s2]; rw [e2]; rfl
      have hnle : N q s1≤K q s1 := by
        have hnot := not_lt_of_ge hm1
        rw [Neighbors.middle_lt_iff q s1 hs1.1] at hnot
        exact le_of_not_gt hnot
      have ht : (1:ℤ)≤Jump.leftFactor q s := by
        have hn : 1≤Jump.leftFactor q s := hp1.2.2
        exact_mod_cast hn
      have hmul : K q s≤(Jump.leftFactor q s:ℤ)*K q s := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right ht hk0.le
      have hmax0 : N q s≤potential q s := le_max_left _ _
      change 2*potential q s2≤potential q s
      rw [hmax2,hn2]
      nlinarith
  · have hp1 := Jump.right_progress q s hq hs hr
    have hm1 : Fraction.value (Neighbors.middle s1)≤hi q := by simpa only [s1,e1] using hp1.2.1
    rcases pending_cases q s1 h2 with ⟨hl2,e2⟩ | ⟨hr2,e2⟩
    · have hp2 := Jump.left_progress q s1 hq hs1 hl2
      have hm2 : lo q≤Fraction.value (Neighbors.middle s2) := by simpa only [s2,e2] using hp2.2.1
      have hc2 : N q s2≤K q s2 := by
        have hnot := not_lt_of_ge hm2
        rw [Neighbors.middle_lt_iff q s2 hs2.1] at hnot
        exact le_of_not_gt hnot
      have hmax2 : potential q s2=K q s2 := max_eq_right hc2
      have hk1 : K q s1=K q s-(Jump.rightFactor q s:ℤ)*N q s := by
        dsimp only [s1]
        rw [e1]
        exact Jump.right_cross _ _ _
      have hn1 : N q s1=N q s := by dsimp only [s1]; rw [e1]; rfl
      have hk2 : K q s2=K q s1 := by dsimp only [s2]; rw [e2]; rfl
      have hkn : K q s1<N q s1 := (Neighbors.middle_lt_iff q s1 hs1.1).mp hl2
      have ht : (1:ℤ)≤Jump.rightFactor q s := by
        have hn : 1≤Jump.rightFactor q s := hp1.2.2
        exact_mod_cast hn
      have hmul : N q s≤(Jump.rightFactor q s:ℤ)*N q s := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right ht hn0.le
      have hmax0 : K q s≤potential q s := le_max_right _ _
      change 2*potential q s2≤potential q s
      rw [hmax2,hk2]
      nlinarith
    · exact False.elim ((not_lt_of_ge hm1) hr2)

theorem done_forever (q : Query) (k r : ℕ) (hk : done («at» q k).2=true) :
    done («at» q (k+r)).2=true := by
  induction r with
  | zero => simpa using hk
  | succ r ih => simpa [Nat.add_assoc] using done_monotone q (k+r) ih
theorem pending_before (q : Query) (j k : ℕ) (hjk : j≤k) (hk : done («at» q k).2=false) :
    done («at» q j).2=false := by
  cases h : done («at» q j).2 with
  | false => rfl
  | true =>
    have ht := done_forever q j (k-j) h
    rw [Nat.add_sub_of_le hjk,hk] at ht
    cases ht

/-- Read the actual saved query from the payload; this is the existing
advance transition, not a supplied successor or a different jump block. -/
private theorem pending_transition (q : Query) (k : ℕ) (hk : done («at» q k).2=false) :
    («at» q (k+1)).2=Jump.step (q,neighbors («at» q k).2) := by
  simp only [«at»,advance,hk,Bool.false_eq_true,if_false,at_source]

theorem at_three_halves (q : Query) (hq : Valid q) (k : ℕ)
    (h0 : done («at» q k).2=false) (h1 : done («at» q (k+1)).2=false)
    (h2 : done («at» q (k+2)).2=false) (h3 : done («at» q (k+3)).2=false) :
    2*potential q (neighbors («at» q (k+2)).2)≤potential q (neighbors («at» q k).2) := by
  have hs := (at_safe q hq k).2.2 h0
  have e1 : («at» q (k+1)).2=Jump.step (q,neighbors («at» q k).2) := pending_transition q k h0
  have e2 : («at» q (k+2)).2=Jump.step (q,neighbors («at» q (k+1)).2) := by
    simpa only [Nat.add_assoc] using pending_transition q (k+1) h1
  have e3 : («at» q (k+3)).2=Jump.step (q,neighbors («at» q (k+2)).2) := by
    simpa only [Nat.add_assoc] using pending_transition q (k+2) h2
  have hd1 : done (Jump.step (q,neighbors («at» q k).2))=false := by rw [← e1]; exact h1
  have hd2 : done (Jump.step (q,neighbors (Jump.step (q,neighbors («at» q k).2))))=false := by
    rw [← e1,← e2]; exact h2
  have hd3 : done (Jump.step (q,neighbors (Jump.step (q,neighbors
      (Jump.step (q,neighbors («at» q k).2))))))=false := by rw [← e1,← e2,← e3]; exact h3
  have hh := three_pending_halves q (neighbors («at» q k).2) hq hs hd1 hd2 hd3
  simpa only [← e1,← e2] using hh

/-- No existence promise is needed for termination: the actual finite run
either returns a rational or certifies there is no bounded-denominator one. -/
theorem complete (q : Query) (hq : Valid q) : done (value q)=true := by
  by_contra h
  have hd : done («at» q (rounds q)).2=false := by
    have hh : done (value q)=false := by cases hc : done (value q) <;> simp_all
    simpa only [value,result_exact] using hh
  let L := (queryEncoding.encode q).length
  have live : ∀ k, k≤rounds q → done («at» q k).2=false := fun k hk => pending_before q k _ hk hd
  have shrink : ∀ m, m≤L → (2:ℤ)^m*potential q (neighbors («at» q (2*m)).2)≤
      potential q (neighbors («at» q 0).2) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      intro hm
      have hi := ih (by omega)
      have hb := at_three_halves q hq (2*m)
        (live _ (by dsimp [rounds,L]; omega)) (live _ (by dsimp [rounds,L]; omega))
        (live _ (by dsimp [rounds,L]; omega)) (live _ (by dsimp [rounds,L]; omega))
      have hp : (0:ℤ)≤2^m := by positivity
      have hmul := mul_le_mul_of_nonneg_left hb hp
      simpa only [show 2*(m+1)=2*m+2 by omega,pow_succ,mul_assoc,mul_comm,mul_left_comm]
        using hmul.trans hi
  have hs0 := (at_safe q hq 0).2.2 (live 0 (by omega))
  have hp0 := positive q _ hq hs0
  have hpbound : potential q (neighbors («at» q 0).2)≤((lo q).den:ℤ) := by
    have he := Potential.at_distance q hq 0
    change N q (neighbors («at» q 0).2)+K q (neighbors («at» q 0).2)≤((lo q).den:ℤ) at he
    change max (N q (neighbors («at» q 0).2)) (K q (neighbors («at» q 0).2))≤((lo q).den:ℤ)
    apply max_le <;> omega
  have hsL := (at_safe q hq (2*L)).2.2 (live _ (by dsimp [rounds,L]; omega))
  have hpL : (1:ℤ)≤potential q (neighbors («at» q (2*L)).2) := by
    have hn := (positive q _ hq hsL).1
    have hb : N q (neighbors («at» q (2*L)).2)≤potential q (neighbors («at» q (2*L)).2) := le_max_left _ _
    omega
  have hlo : (lo q).den<2^L := Nat.size_le.mp (GlobalBounds.denominator_bits q)
  have hlo' : ((lo q).den:ℤ)<(2:ℤ)^L := by exact_mod_cast hlo
  have hm := (shrink L le_rfl).trans hpbound
  have hp : (0:ℤ)≤2^L := by positivity
  have hh := mul_le_mul_of_nonneg_left hpL hp
  simp only [mul_one] at hh
  omega
end Termination
end Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.RationalExtraction
