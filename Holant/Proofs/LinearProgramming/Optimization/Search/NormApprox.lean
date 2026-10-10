import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
An actual rational upper approximation to a positive square root. Only the
integer square root is evaluated; Real.sqrt occurs exclusively in proofs.
The precision parameter is a binary integer, never a unary enumeration bound.
NormProgram connects this exact formula to the existing bitwise Nat.sqrt machine.
-/
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Optimization.Search.NormApprox

def numerator (p q T : ℕ) : ℕ := Nat.sqrt (p*q*T^2)+1
def fraction (p q T : ℕ) : ℚ := (numerator p q T : ℚ)/(q*T : ℕ)
def value (s : ℚ) (T : ℕ) : ℚ := fraction s.num.natAbs s.den T

theorem fraction_pos (p q T : ℕ) (hq : 0<q) (hT : 0<T) :
    0<fraction p q T := by
  unfold fraction numerator
  positivity

/-- Both error bounds are consequences of the two integer-square-root
inequalities for the number actually used by `fraction`. -/
theorem fraction_bounds (p q T : ℕ) (hp : 0<p) (hq : 0<q) (hT : 0<T) :
    Real.sqrt ((p:ℝ)/q) ≤ (fraction p q T:ℝ) ∧
    (fraction p q T:ℝ) ≤ (1+1/(T:ℝ))*Real.sqrt ((p:ℝ)/q) := by
  let r := Real.sqrt ((p:ℝ)/q)
  let k := Nat.sqrt (p*q*T^2)
  have hp' : (0:ℝ)<p := by exact_mod_cast hp
  have hq' : (0:ℝ)<q := by exact_mod_cast hq
  have hT' : (0:ℝ)<T := by exact_mod_cast hT
  have hr : 0≤r := Real.sqrt_nonneg _
  have hr2 : r^2=(p:ℝ)/q := Real.sq_sqrt (by positivity)
  have hrq : r^2*(q:ℝ)=p := by rw [hr2]; field_simp
  have hs : (r*((q:ℝ)*T))^2=(p:ℝ)*q*T^2 := by
    calc
      _ = (r^2*(q:ℝ))*((q:ℝ)*T^2) := by ring
      _ = _ := by rw [hrq]; ring
  have hk0 : (0:ℝ)≤k := by positivity
  have hk : (k:ℝ)^2≤(p:ℝ)*q*T^2 := by
    exact_mod_cast Nat.sqrt_le' (p*q*T^2)
  have hk' : (p:ℝ)*q*T^2<((k:ℝ)+1)^2 := by
    exact_mod_cast Nat.lt_succ_sqrt' (p*q*T^2)
  have hx : 0<(q:ℝ)*T := mul_pos hq' hT'
  have hrx : 0≤r*((q:ℝ)*T) := mul_nonneg hr hx.le
  have hlow : (k:ℝ)≤r*((q:ℝ)*T) := by nlinarith
  have hupp : r*((q:ℝ)*T)≤(k:ℝ)+1 := by nlinarith
  have hf : (fraction p q T:ℝ)=((k:ℝ)+1)/((q:ℝ)*T) := by
    simp [fraction,numerator,k]
  have hp1 : (1:ℝ)≤p := by exact_mod_cast hp
  have hq1 : (1:ℝ)≤q := by exact_mod_cast hq
  have hpq : (1:ℝ)≤(p:ℝ)*q := by
    simpa using mul_le_mul hp1 hq1 (by norm_num : (0:ℝ)≤1) hp'.le
  have hrq2 : (r*(q:ℝ))^2=(p:ℝ)*q := by
    calc
      _ = (r^2*(q:ℝ))*(q:ℝ) := by ring
      _ = _ := by rw [hrq]
  have hrq1 : 1≤r*(q:ℝ) := by
    have : 0≤r*(q:ℝ) := mul_nonneg hr hq'.le
    nlinarith
  have hinv : 1/(q:ℝ)≤r := (div_le_iff₀ hq').mpr hrq1
  rw [hf]
  constructor
  · exact (le_div_iff₀ hx).mpr hupp
  · calc
      ((k:ℝ)+1)/((q:ℝ)*T) ≤ r+1/((q:ℝ)*T) := by
        apply (div_le_iff₀ hx).mpr
        have he : (r+1/((q:ℝ)*T))*((q:ℝ)*T)=r*((q:ℝ)*T)+1 := by
          field_simp
        rw [he]
        linarith
      _ = r+(1/(q:ℝ))/(T:ℝ) := by field_simp
      _ ≤ r+r/(T:ℝ) := add_le_add (le_refl r) (div_le_div_of_nonneg_right hinv hT'.le)
      _ = (1+1/(T:ℝ))*r := by ring

theorem value_pos (s : ℚ) (T : ℕ) (hT : 0<T) : 0<value s T :=
  fraction_pos _ _ _ s.den_pos hT

theorem positive_fraction (s : ℚ) (hs : 0<s) :
    (s.num.natAbs:ℚ)/(s.den:ℚ)=s := by
  have hn : 0≤s.num := (Rat.num_pos.mpr hs).le
  have he : (s.num.natAbs:ℤ)=s.num := Int.natAbs_of_nonneg hn
  have he' : (s.num.natAbs:ℚ)=(s.num:ℚ) := by
    simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z : ℚ)) he
  rw [he',Rat.num_div_den]

theorem bounds (s : ℚ) (hs : 0<s) (T : ℕ) (hT : 0<T) :
    Real.sqrt (s:ℝ) ≤ (value s T:ℝ) ∧
    (value s T:ℝ) ≤ (1+1/(T:ℝ))*Real.sqrt (s:ℝ) := by
  have hp : 0<s.num.natAbs := Int.natAbs_pos.mpr (ne_of_gt (Rat.num_pos.mpr hs))
  have he : (s.num.natAbs:ℝ)/(s.den:ℝ)=(s:ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_natCast] using
      congrArg (fun q : ℚ => (q : ℝ)) (positive_fraction s hs)
  simpa only [he,value] using fraction_bounds s.num.natAbs s.den T hp s.den_pos hT

end Holant.LocalDrafts.RemoteWork.RationalLP.Optimization.Search.NormApprox
