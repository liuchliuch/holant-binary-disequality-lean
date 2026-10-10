import Holant.Proofs.Hardness.ThreeModeChain
import Mathlib.Analysis.Normed.Field.Basic

/-! Method limitation, not a manuscript counterexample: positive strict-triangle
triples are preserved by every ordered two-edge series composition. In
particular the proposed two-copy escape cannot reach real norm dominance. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.ThreeModeTriangleObstruction
open Holant
open Holant.LocalDrafts.Hardness.EightVertexNonexception
set_option backward.isDefEq.respectTransparency false

/-- Strict triangle region for positive original coefficients. -/
def Triangle (a b c : ℝ) : Prop :=
  0<a ∧ 0<b ∧ 0<c ∧ a<b+c ∧ b<a+c ∧ c<a+b

/-- Literal actual contraction law, without a presumed transfer matrix. -/
theorem series_original {K : Type} [Field K] (N M : Network K 4) (a b c p q r : K)
    (hN : N.denote=ThreeModeSignatures.original a b c)
    (hM : M.denote=ThreeModeSignatures.original p q r) :
    (ExactTwoChain.series N M).denote=
      ThreeModeSignatures.original (a*q+b*p) (a*p+b*q) (c*r) := by
  funext x
  rw [ExactTwoChain.series_denote,hN,hM]
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [ThreeModeSignatures.original,table,h0,h1,h2,h3] <;> ring

namespace R
export Holant.Complexity.BinaryInterpolation.Chains (reindex reindex_denote)
end R

/-- These are actual original-port permutations, not dictionary substitutions. -/
theorem swap_bc {K : Type} [Field K] (a b c : K) :
    Tensor.reindex SignedTwoCoefficientSignatures.middleSwap (ThreeModeSignatures.original a b c)=
      ThreeModeSignatures.original a c b := by
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [Tensor.reindex_apply,SignedTwoCoefficientSignatures.middleSwap,
      ThreeModeSignatures.original,table,h0,h1,h2,h3]

theorem swap_ac {K : Type} [Field K] (a b c : K) :
    Tensor.reindex TwoCoefficientSignatures.middleSwap (ThreeModeSignatures.original a b c)=
      ThreeModeSignatures.original c b a := by
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [Tensor.reindex_apply,TwoCoefficientSignatures.middleSwap,
      ThreeModeSignatures.original,table,h0,h1,h2,h3]

/-- Two original corollas, two native-X edges, and literal boundary permutations. -/
def escapeNetwork {K : Type} [Field K] (a b d : K) : Network K 4 :=
  let N := R.reindex (Network.corolla (ThreeModeSignatures.original a b d))
    SignedTwoCoefficientSignatures.middleSwap
  let M := R.reindex N TwoCoefficientSignatures.middleSwap
  R.reindex (R.reindex (ExactTwoChain.series N M) TwoCoefficientSignatures.middleSwap)
    SignedTwoCoefficientSignatures.middleSwap

theorem escape_network_denote {K : Type} [Field K] (a b d : K) :
    (escapeNetwork a b d).denote=
      ThreeModeSignatures.original (a*b) (d*(a+b)) (a*b+d^2) := by
  let N := R.reindex (Network.corolla (ThreeModeSignatures.original a b d))
    SignedTwoCoefficientSignatures.middleSwap
  let M := R.reindex N TwoCoefficientSignatures.middleSwap
  have hN : N.denote=ThreeModeSignatures.original a d b := by
    dsimp only [N]
    rw [R.reindex_denote,Network.denote_corolla,swap_bc]
  have hM : M.denote=ThreeModeSignatures.original b d a := by
    dsimp only [M]
    rw [R.reindex_denote,hN,swap_ac]
  change (R.reindex (R.reindex (ExactTwoChain.series N M)
    TwoCoefficientSignatures.middleSwap) SignedTwoCoefficientSignatures.middleSwap).denote=_
  rw [R.reindex_denote,R.reindex_denote,series_original N M a d b b d a hN hM,swap_ac,swap_bc]
  congr 1 <;> ring

theorem escape_network_counts {K : Type} [Field K] (a b d : K) :
    (escapeNetwork a b d).shape.vertices=2 ∧ (escapeNetwork a b d).shape.edges=2 := by
  constructor <;> rfl

/-- Applies to different positive input triples, hence to arbitrary series trees. -/
theorem series_triangle {a b c p q r : ℝ} (h : Triangle a b c) (h' : Triangle p q r) :
    Triangle (a*q+b*p) (a*p+b*q) (c*r) := by
  obtain ⟨ha,hb,hc,hab,hba,hcab⟩ := h
  obtain ⟨hp,hq,hr,hpq,hqp,hrpq⟩ := h'
  have habs : |a-b|<c := abs_lt.mpr ⟨by linarith,by linarith⟩
  have hpqs : |p-q|<r := abs_lt.mpr ⟨by linarith,by linarith⟩
  have hprod : |(a-b)*(p-q)|<c*r := by
    rw [abs_mul]
    calc
      |a-b| * |p-q|≤|a-b| * r := mul_le_mul_of_nonneg_left hpqs.le (abs_nonneg _)
      _<c*r := mul_lt_mul_of_pos_right habs hr
  have hsum : c*r<(a+b)*(p+q) := by
    calc
      c*r<(a+b)*r := mul_lt_mul_of_pos_right hcab hr
      _≤(a+b)*(p+q) := mul_le_mul_of_nonneg_left hrpq.le (by positivity)
  have hupper := le_abs_self ((a-b)*(p-q))
  have hlower := neg_abs_le ((a-b)*(p-q))
  refine ⟨by positivity,by positivity,by positivity,?_,?_,?_⟩ <;> nlinarith

/-- The region is unchanged by swapping or cyclically permuting coefficients. -/
theorem swap_triangle {a b c : ℝ} (h : Triangle a b c) : Triangle b a c := by
  unfold Triangle at *
  rcases h with ⟨ha,hb,hc,h1,h2,h3⟩
  exact ⟨hb,ha,hc,h2,h1,by linarith⟩

theorem rotate_triangle {a b c : ℝ} (h : Triangle a b c) : Triangle b c a := by
  unfold Triangle at *
  rcases h with ⟨ha,hb,hc,h1,h2,h3⟩
  exact ⟨hb,hc,ha,by linarith,by linarith,h1⟩

/-- Proposed two-copy map, in the original coefficient ordering. -/
def escape (a b d : ℝ) : ℝ×ℝ×ℝ := (a*b,d*(a+b),a*b+d^2)

theorem escape_triangle {a b d : ℝ} (h : Triangle a b d) :
    Triangle (escape a b d).1 (escape a b d).2.1 (escape a b d).2.2 := by
  have h1 : Triangle a d b := rotate_triangle (swap_triangle h)
  have h2 : Triangle b d a := rotate_triangle h
  have hs := series_triangle h1 h2
  have ht := rotate_triangle (rotate_triangle hs)
  simpa only [escape,pow_two,mul_comm,mul_add,add_comm,add_left_comm,add_assoc] using ht

/-- No iterate of this map can leave the strict triangle region. -/
def stage (a b d : ℝ) : ℕ → ℝ×ℝ×ℝ
  | 0=>(a,b,d)
  | k+1=>escape (stage a b d k).1 (stage a b d k).2.1 (stage a b d k).2.2

theorem stage_triangle {a b d : ℝ} (h : Triangle a b d) (k : ℕ) :
    Triangle (stage a b d k).1 (stage a b d k).2.1 (stage a b d k).2.2 := by
  induction k with
  | zero=>exact h
  | succ k ih=>exact escape_triangle ih

theorem not_dominant {a b c : ℝ} (h : Triangle a b c) : ¬‖a+b‖<‖c‖ := by
  rcases h with ⟨ha,hb,hc,_,_,ht⟩
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos (by positivity : 0<a+b),abs_of_pos hc]
  exact not_lt_of_ge ht.le

theorem fixture_triangle : Triangle 1 2 (5/2) := by norm_num [Triangle]
theorem fixture_step : escape 1 2 (5/2)=(2,15/2,33/4) := by norm_num [escape]
theorem fixture_no_escape (k : ℕ) :
    ¬‖(stage 1 2 (5/2) k).1+(stage 1 2 (5/2) k).2.1‖<‖(stage 1 2 (5/2) k).2.2‖ :=
  not_dominant (stage_triangle fixture_triangle k)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.ThreeModeTriangleObstruction
