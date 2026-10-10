import Holant.Proofs.LinearProgramming.Recovery.RationalExtraction.Codec

set_option autoImplicit false

/-! Kernel-checked recovery component. Adjacent signed fractions are the Euclidean search
certificate. Their determinant is exactly one. Every rational strictly
between them has denominator at least the sum of their denominators.
-/
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.RationalExtraction
open Holant.LocalDrafts.TraversalCompletion.RationalLP
namespace Fraction
def value (f : Fraction) : ℚ := mkRat f.1 f.2
theorem value_eq (f : Fraction) : value f=(f.1:ℚ)/(f.2:ℚ) := Rat.mkRat_eq_div _ _
theorem denominator_le (f : Fraction) (h : 0<f.2) : (value f).den≤f.2 := by
  rw [value,Rat.mkRat_eq_divInt]
  simpa using Holant.Algebraic.divInt_den_le f.1 (f.2:ℤ) (by exact_mod_cast Nat.ne_of_gt h)
def lowerCross (q : ℚ) (f : Fraction) : ℤ := q.num*(f.2:ℤ)-f.1*(q.den:ℤ)
def upperCross (q : ℚ) (f : Fraction) : ℤ := f.1*(q.den:ℤ)-q.num*(f.2:ℤ)

theorem lowerCross_pos (q : ℚ) (f : Fraction) (hf : 0<f.2) :
    0<lowerCross q f ↔ value f<q := by
  have hq : (0:ℚ)<q.den := by exact_mod_cast q.den_pos
  have hd : (0:ℚ)<f.2 := by exact_mod_cast hf
  rw [value_eq]
  conv_rhs => rw [← Rat.num_div_den q]
  rw [div_lt_div_iff₀ hd hq]
  have hc : (0:ℚ)<(lowerCross q f:ℚ) ↔ (f.1:ℚ)*q.den<(q.num:ℚ)*f.2 := by
    dsimp [lowerCross]
    push_cast
    constructor <;> intro h <;> linarith
  exact (by exact_mod_cast hc)
theorem upperCross_pos (q : ℚ) (f : Fraction) (hf : 0<f.2) :
    0<upperCross q f ↔ q<value f := by
  have hq : (0:ℚ)<q.den := by exact_mod_cast q.den_pos
  have hd : (0:ℚ)<f.2 := by exact_mod_cast hf
  rw [value_eq]
  conv_rhs => rw [← Rat.num_div_den q]
  rw [div_lt_div_iff₀ hq hd]
  have hc : (0:ℚ)<(upperCross q f:ℚ) ↔ (q.num:ℚ)*f.2<(f.1:ℚ)*q.den := by
    dsimp [upperCross]
    push_cast
    constructor <;> intro h <;> linarith
  exact (by exact_mod_cast hc)
end Fraction

namespace Neighbors
def adjacent (s : Neighbors) : Prop :=
  0<s.1.2 ∧ 0<s.2.2 ∧ s.2.1*(s.1.2:ℤ)-s.1.1*(s.2.2:ℤ)=1
def Brackets (q : Query) (s : Neighbors) : Prop :=
  adjacent s ∧ Fraction.value s.1<lo q ∧ hi q<Fraction.value s.2
def middle (s : Neighbors) : Fraction := (s.1.1+s.2.1,s.1.2+s.2.2)
def leftJump (s : Neighbors) (t : ℕ) : Neighbors :=
  ((s.1.1+(t:ℤ)*s.2.1,s.1.2+t*s.2.2),s.2)
def rightJump (s : Neighbors) (t : ℕ) : Neighbors :=
  (s.1,(s.2.1+(t:ℤ)*s.1.1,s.2.2+t*s.1.2))

theorem middle_positive (s : Neighbors) (h : adjacent s) : 0<(middle s).2 := by
  rcases h with ⟨hb,hd,he⟩
  dsimp [middle]
  omega
theorem left_adjacent (s : Neighbors) (h : adjacent s) (t : ℕ) : adjacent (leftJump s t) := by
  rcases h with ⟨hb,hd,he⟩
  refine ⟨by dsimp [leftJump]; positivity,hd,?_⟩
  dsimp [leftJump]
  push_cast
  nlinarith
theorem right_adjacent (s : Neighbors) (h : adjacent s) (t : ℕ) : adjacent (rightJump s t) := by
  rcases h with ⟨hb,hd,he⟩
  refine ⟨hb,by dsimp [rightJump]; positivity,?_⟩
  dsimp [rightJump]
  push_cast
  nlinarith

theorem denominator_identity (s : Neighbors) (h : adjacent s) (r : ℚ) :
    (r.den:ℤ)=(s.2.2:ℤ)*Fraction.lowerCross r s.1+
      (s.1.2:ℤ)*Fraction.upperCross r s.2 := by
  have he := h.2.2
  dsimp [Fraction.lowerCross,Fraction.upperCross]
  nlinarith

theorem denominator_lower_bound (s : Neighbors) (h : adjacent s) (r : ℚ)
    (hl : Fraction.value s.1<r) (hr : r<Fraction.value s.2) : s.1.2+s.2.2≤r.den := by
  have hn := (Fraction.lowerCross_pos r s.1 h.1).mpr hl
  have hk := (Fraction.upperCross_pos r s.2 h.2.1).mpr hr
  have he := denominator_identity s h r
  have hb : (0:ℤ)<s.1.2 := by exact_mod_cast h.1
  have hd : (0:ℤ)<s.2.2 := by exact_mod_cast h.2.1
  have hle : (s.1.2:ℤ)+s.2.2≤r.den := by nlinarith
  exact_mod_cast hle

theorem cap_excludes (q : Query) (s : Neighbors) (hq : Valid q) (hs : Brackets q s)
    (hcap : cap q<s.1.2+s.2.2) : ¬∃ r, Candidate q r := by
  rintro ⟨r,hl,hr,hd⟩
  have hb := denominator_lower_bound s hs.1 r (lt_of_lt_of_le hs.2.1 hl)
    (lt_of_le_of_lt hr hs.2.2)
  omega

theorem middle_cross (r : ℚ) (s : Neighbors) :
    Fraction.lowerCross r (middle s)=Fraction.lowerCross r s.1-Fraction.upperCross r s.2 := by
  dsimp [Fraction.lowerCross,Fraction.upperCross,middle]
  push_cast
  ring
theorem middle_lt_iff (q : Query) (s : Neighbors) (hs : adjacent s) :
    Fraction.value (middle s)<lo q ↔ Fraction.upperCross (lo q) s.2<Fraction.lowerCross (lo q) s.1 := by
  rw [← Fraction.lowerCross_pos (lo q) (middle s) (middle_positive s hs),middle_cross]
  omega
theorem lt_middle_iff (q : Query) (s : Neighbors) (hs : adjacent s) :
    hi q<Fraction.value (middle s) ↔ Fraction.lowerCross (hi q) s.1<Fraction.upperCross (hi q) s.2 := by
  rw [← Fraction.upperCross_pos (hi q) (middle s) (middle_positive s hs)]
  have he : Fraction.upperCross (hi q) (middle s)=
      Fraction.upperCross (hi q) s.2-Fraction.lowerCross (hi q) s.1 := by
    dsimp [Fraction.lowerCross,Fraction.upperCross,middle]
    push_cast
    ring
  rw [he]
  omega
end Neighbors
end Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.RationalExtraction
