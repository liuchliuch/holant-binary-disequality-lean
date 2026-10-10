import Holant.Proofs.Hardness.ThreeModeChain
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic

/-! The positive triangle-equality boundary has a literal hard two-coefficient
row H. H and J below are proof coordinates, not free oracle gadgets. The actual
positive original-q chain is used by the interpolation compiler. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.PositiveBoundarySignatures
open Holant
variable {K : Type*} [Field K] [CharZero K]

def H : Signature K 4 := TwoCoefficientSignatures.weighted 1 (1/2)
def J : Signature K 4 := (-1/2 : K) • SignedTwoCoefficientSignatures.Bminus

theorem spectral_boundary (c nu : K) :
    ThreeModeSignatures.spectral c c nu=c • H+nu • J := by
  rw [ThreeModeSignatures.spectral_linear]
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [H,J,TwoCoefficientSignatures.weighted,ExactTwoSignatures.E,ExactTwoSignatures.B,
      SignedTwoCoefficientSignatures.Bminus,Holant.LocalDrafts.Hardness.EightVertexNonexception.table,
      h0,h1,h2,h3]

theorem original_boundary (a b c : K) (hc : c=a+b) :
    ThreeModeSignatures.original a b c=c • H+(b-a) • J := by
  rw [ThreeModeSignatures.original_spectral,←hc,spectral_boundary]

theorem normalized (a b c : K) (hc : c=a+b) (hnu : b-a≠0) (k : ℕ) :
    ThreeModeSignatures.spectral (c^(k+1)) ((a+b)^(k+1)) ((b-a)^(k+1))=
      (b-a)^k • ((b-a) • J+(c/(b-a))^k • (c • H)) := by
  rw [←hc,spectral_boundary]
  funext x
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,div_pow,pow_succ]
  field_simp
  ring

section Ordered
variable [LinearOrder K] [IsStrictOrderedRing K]

/-- Strict positivity supplies both sign branches of the required modulus gap. -/
theorem abs_gap (a b c : K) (ha : 0<a) (hb : 0<b) (hc : c=a+b) :
    |b-a|<c := by
  rw [abs_lt]
  constructor <;> linarith

theorem ratio_abs_gt_one (a b c : K) (ha : 0<a) (hb : 0<b)
    (hc : c=a+b) (hnu : b-a≠0) : 1 < |c/(b-a)| := by
  have hcpos : 0<c := by rw [hc]; exact add_pos ha hb
  rw [abs_div,abs_of_pos hcpos]
  exact (lt_div_iff₀ (abs_pos.mpr hnu)).2 (by simpa using abs_gap a b c ha hb hc)

/-- No infinite-order certificate is accepted as input at the positive endpoint. -/
theorem infinite_ratio (a b c : K) (ha : 0<a) (hb : 0<b)
    (hc : c=a+b) (hnu : b-a≠0) : ∀n : ℕ,0<n → (c/(b-a))^n≠1 := by
  intro n hn he
  have hlt : 1 < |c/(b-a)|^n := one_lt_pow₀ (ratio_abs_gt_one a b c ha hb hc hnu) (Nat.ne_of_gt hn)
  have habs := congrArg abs he
  rw [abs_pow,abs_one] at habs
  exact (ne_of_gt hlt) habs

end Ordered
end Holant.LocalDrafts.RemoteWork.HardnessChainV1.PositiveBoundarySignatures
