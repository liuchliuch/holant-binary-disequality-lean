import Holant.Proofs.LinearProgramming.Recovery.RationalExtraction.Euclidean
import Holant.Proofs.LinearProgramming.Recovery.RationalExtraction.Neighbors

set_option autoImplicit false

/-! Kernel-checked recovery component. Maximal Euclidean jumps preserve the strict enclosing
neighbors. The quotient is (N-1)/K rather than N/K: equality with a closed
endpoint must remain inside the searched interval, not be skipped.
-/
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.RationalExtraction
open Holant.LocalDrafts.TraversalCompletion.RationalLP
namespace Jump
def leftFactor (q : Query) (s : Neighbors) : ℕ :=
  DivMod.jump (Fraction.lowerCross (lo q) s.1).toNat (Fraction.upperCross (lo q) s.2).toNat
def rightFactor (q : Query) (s : Neighbors) : ℕ :=
  DivMod.jump (Fraction.upperCross (hi q) s.2).toNat (Fraction.lowerCross (hi q) s.1).toNat

theorem left_cross (q : ℚ) (s : Neighbors) (t : ℕ) :
    Fraction.lowerCross q (Neighbors.leftJump s t).1=
      Fraction.lowerCross q s.1-(t:ℤ)*Fraction.upperCross q s.2 := by
  dsimp [Fraction.lowerCross,Fraction.upperCross,Neighbors.leftJump]
  push_cast
  ring
theorem right_cross (q : ℚ) (s : Neighbors) (t : ℕ) :
    Fraction.upperCross q (Neighbors.rightJump s t).2=
      Fraction.upperCross q s.2-(t:ℤ)*Fraction.lowerCross q s.1 := by
  dsimp [Fraction.lowerCross,Fraction.upperCross,Neighbors.rightJump]
  push_cast
  ring

/-- Signed exact form of the quotient/remainder residual. -/
theorem residual_identity (N K : ℤ) (hN : 0<N) (hK : 0<K) :
    N-(DivMod.jump N.toNat K.toNat:ℤ)*K=(DivMod.residual N.toNat K.toNat:ℤ) := by
  have hn : 0<N.toNat := Int.pos_iff_toNat_pos.mp hN
  have hs := DivMod.split N.toNat K.toNat hn
  have hnc : (N.toNat:ℤ)=N := Int.toNat_of_nonneg hN.le
  have hkc : (K.toNat:ℤ)=K := Int.toNat_of_nonneg hK.le
  have hs' : N=(DivMod.jump N.toNat K.toNat:ℤ)*K+
      (DivMod.residual N.toNat K.toNat:ℤ) := by
    have hc : (N.toNat:ℤ)=(DivMod.jump N.toNat K.toNat:ℤ)*(K.toNat:ℤ)+
        (DivMod.residual N.toNat K.toNat:ℤ) := by exact_mod_cast hs
    simpa only [hnc,hkc] using hc
  linarith

theorem left_progress (q : Query) (s : Neighbors) (hq : Valid q) (hs : Neighbors.Brackets q s)
    (hm : Fraction.value (Neighbors.middle s)<lo q) :
    Neighbors.Brackets q (Neighbors.leftJump s (leftFactor q s)) ∧
      lo q≤Fraction.value (Neighbors.middle (Neighbors.leftJump s (leftFactor q s))) ∧
      0<leftFactor q s := by
  let N := Fraction.lowerCross (lo q) s.1
  let K := Fraction.upperCross (lo q) s.2
  have hn : 0<N := (Fraction.lowerCross_pos _ _ hs.1.1).mpr hs.2.1
  have hk : 0<K := (Fraction.upperCross_pos _ _ hs.1.2.1).mpr (lt_of_le_of_lt hq.1 hs.2.2)
  have hkn : K<N := (Neighbors.middle_lt_iff q s hs.1).mp hm
  have he := residual_identity N K hn hk
  have hrp : (0:ℤ)<DivMod.residual N.toNat K.toNat := by
    exact_mod_cast DivMod.residual_pos N.toNat K.toNat
  have hrl : (DivMod.residual N.toNat K.toNat:ℤ)≤K := by
    have h := DivMod.residual_le N.toNat K.toNat (Int.pos_iff_toNat_pos.mp hk)
    have hc : (DivMod.residual N.toNat K.toNat:ℤ)≤(K.toNat:ℤ) := by exact_mod_cast h
    simpa only [Int.toNat_of_nonneg hk.le] using hc
  have ha := Neighbors.left_adjacent s hs.1 (leftFactor q s)
  have hx : Fraction.lowerCross (lo q) (Neighbors.leftJump s (leftFactor q s)).1=
      (DivMod.residual N.toNat K.toNat:ℤ) := by
    rw [left_cross]
    exact he
  have hbr : Neighbors.Brackets q (Neighbors.leftJump s (leftFactor q s)) :=
    ⟨ha,(Fraction.lowerCross_pos _ _ ha.1).mp (by rw [hx]; exact hrp),hs.2.2⟩
  refine ⟨hbr,?_,?_⟩
  · apply le_of_not_gt
    intro h
    have h' := (Neighbors.middle_lt_iff q _ ha).mp h
    change K<Fraction.lowerCross (lo q) (Neighbors.leftJump s (leftFactor q s)).1 at h'
    rw [hx] at h'
    omega
  · exact DivMod.jump_pos N.toNat K.toNat (Int.pos_iff_toNat_pos.mp hk)
      ((Int.toNat_lt_toNat hn).mpr hkn)

theorem right_progress (q : Query) (s : Neighbors) (hq : Valid q) (hs : Neighbors.Brackets q s)
    (hm : hi q<Fraction.value (Neighbors.middle s)) :
    Neighbors.Brackets q (Neighbors.rightJump s (rightFactor q s)) ∧
      Fraction.value (Neighbors.middle (Neighbors.rightJump s (rightFactor q s)))≤hi q ∧
      0<rightFactor q s := by
  let N := Fraction.lowerCross (hi q) s.1
  let K := Fraction.upperCross (hi q) s.2
  have hn : 0<N := (Fraction.lowerCross_pos _ _ hs.1.1).mpr (lt_of_lt_of_le hs.2.1 hq.1)
  have hk : 0<K := (Fraction.upperCross_pos _ _ hs.1.2.1).mpr hs.2.2
  have hnk : N<K := (Neighbors.lt_middle_iff q s hs.1).mp hm
  have he := residual_identity K N hk hn
  have hrp : (0:ℤ)<DivMod.residual K.toNat N.toNat := by
    exact_mod_cast DivMod.residual_pos K.toNat N.toNat
  have hrl : (DivMod.residual K.toNat N.toNat:ℤ)≤N := by
    have h := DivMod.residual_le K.toNat N.toNat (Int.pos_iff_toNat_pos.mp hn)
    have hc : (DivMod.residual K.toNat N.toNat:ℤ)≤(N.toNat:ℤ) := by exact_mod_cast h
    simpa only [Int.toNat_of_nonneg hn.le] using hc
  have ha := Neighbors.right_adjacent s hs.1 (rightFactor q s)
  have hx : Fraction.upperCross (hi q) (Neighbors.rightJump s (rightFactor q s)).2=
      (DivMod.residual K.toNat N.toNat:ℤ) := by
    rw [right_cross]
    exact he
  have hbr : Neighbors.Brackets q (Neighbors.rightJump s (rightFactor q s)) :=
    ⟨ha,hs.2.1,(Fraction.upperCross_pos _ _ ha.2.1).mp (by rw [hx]; exact hrp)⟩
  refine ⟨hbr,?_,?_⟩
  · apply le_of_not_gt
    intro h
    have h' := (Neighbors.lt_middle_iff q _ ha).mp h
    change N<Fraction.upperCross (hi q) (Neighbors.rightJump s (rightFactor q s)).2 at h'
    rw [hx] at h'
    omega
  · exact DivMod.jump_pos K.toNat N.toNat (Int.pos_iff_toNat_pos.mp hn)
      ((Int.toNat_lt_toNat hk).mpr hnk)

def step (v : StepInput) : Result :=
  let q := v.1
  let s := v.2
  if cap q<s.1.2+s.2.2 then miss s
  else if Fraction.value (Neighbors.middle s)<lo q then
    pending (Neighbors.leftJump s (leftFactor q s))
  else if hi q<Fraction.value (Neighbors.middle s) then
    pending (Neighbors.rightJump s (rightFactor q s))
  else hit (Fraction.value (Neighbors.middle s)) s

def Safe (q : Query) (r : Result) : Prop :=
  (done r=true → found r=true → Candidate q (answer r)) ∧
  (done r=true → found r=false → ¬∃ x, Candidate q x) ∧
  (done r=false → Neighbors.Brackets q (neighbors r))

theorem step_safe (q : Query) (s : Neighbors) (hq : Valid q) (hs : Neighbors.Brackets q s) :
    Safe q (step (q,s)) := by
  by_cases hc : cap q<s.1.2+s.2.2
  · simp only [step,hc,if_pos,Safe,done,found,miss,answer,neighbors]
    exact ⟨by simp,by intro _ _; exact Neighbors.cap_excludes q s hq hs hc,by simp⟩
  · by_cases hl : Fraction.value (Neighbors.middle s)<lo q
    · have hp := (left_progress q s hq hs hl).1
      simp only [step,hc,if_neg,hl,if_pos,Safe,done,found,pending,answer,neighbors]
      exact ⟨by simp,by simp,by intro _; exact hp⟩
    · by_cases hr : hi q<Fraction.value (Neighbors.middle s)
      · have hp := (right_progress q s hq hs hr).1
        simp only [step,hc,if_neg,hl,hr,if_pos,Safe,done,found,pending,answer,neighbors]
        exact ⟨by simp,by simp,by intro _; exact hp⟩
      · have hd := Fraction.denominator_le (Neighbors.middle s) (Neighbors.middle_positive s hs.1)
        have hcap : (Neighbors.middle s).2≤cap q := by
          change s.1.2+s.2.2≤cap q
          exact le_of_not_gt hc
        have hx : Candidate q (Fraction.value (Neighbors.middle s)) :=
          ⟨le_of_not_gt hl,le_of_not_gt hr,hd.trans hcap⟩
        simp only [step,hc,if_neg,hl,hr,Safe,done,found,hit,answer,neighbors]
        exact ⟨by intro _ _; exact hx,by simp,by simp⟩

/-- A promised interval point is not an input value. If it exists, this
physical block either returns a valid answer or preserves the search domain. -/
theorem step_complete_or_pending (q : Query) (s : Neighbors) (hq : Valid q)
    (hs : Neighbors.Brackets q s) (hex : ∃ r, Candidate q r) :
    (done (step (q,s))=true ∧ found (step (q,s))=true ∧ Candidate q (answer (step (q,s)))) ∨
      (done (step (q,s))=false ∧ Neighbors.Brackets q (neighbors (step (q,s)))) := by
  have h := step_safe q s hq hs
  cases hd : done (step (q,s)) with
  | false => exact Or.inr ⟨rfl,h.2.2 hd⟩
  | true =>
    cases hf : found (step (q,s)) with
    | false => exact False.elim (h.2.1 hd hf hex)
    | true => exact Or.inl ⟨rfl,rfl,h.1 hd hf⟩
end Jump
end Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.RationalExtraction
