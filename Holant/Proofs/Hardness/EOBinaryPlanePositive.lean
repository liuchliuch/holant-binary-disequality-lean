import Holant.Proofs.Hardness.EOBinaryPlaneFlat
import Holant.Proofs.Hardness.EOBinaryPlaneClassification

/-! Exhaustive five-form coefficient producer for nonexceptional full binary
tables. The alternatives are original, transpose, Hadamard square, and original
weighted by its row-sum or column-sum unary. Their Gram norm tables are genuinely
positive and nonsingular. Oracle availability is deliberately not assumed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlanePositive
open Holant Holant.Tractable
namespace G
export EOBinaryPlaneGram (determinant cross table table_positive_nonsingular square_route)
end G
namespace F
export EOBinaryPlaneFlat (row_or_column_sums weighted_route)
end F
set_option backward.isDefEq.respectTransparency false

def Good (f : Signature ℝ 2) : Prop :=
  (∀z,0<f z) ∧ 0<f ![false,false]*f ![true,true]-f ![false,true]*f ![true,false]

def exceptional (a b c d : ℂ) : Prop :=
  a^4=b^4 ∧ a^4=c^4 ∧ a^4=d^4 ∧ a*d=-(b*c)

def candidate (a b c d : ℂ) (i : Fin 5) : Signature ℝ 2 :=
  ![G.table a b c d,G.table a c b d,G.table (a^2) (b^2) (c^2) (d^2),
    G.table (a*(a+b)) (b*(c+d)) (c*(a+b)) (d*(c+d)),
    G.table (a*(a+c)) (b*(b+d)) (c*(a+c)) (d*(b+d))] i

theorem exists_good (a b c d : ℂ) (ha : a≠0) (hb : b≠0) (hc : c≠0)
    (hd : G.determinant a b c d≠0) (he : ¬exceptional a b c d) :
    ∃i : Fin 5,Good (candidate a b c d i) := by
  by_cases hx : G.cross a b c d=0
  · by_cases ht : G.cross a c b d=0
    · by_cases hs : a*d+b*c=0
      · have hbad : a^4≠b^4 ∨ a^4≠c^4 ∨ a^4≠d^4 := by
          by_contra hn
          push Not at hn
          exact he ⟨hn.1,hn.2.1,hn.2.2,eq_neg_of_add_eq_zero_left hs⟩
        rcases F.row_or_column_sums a b c d ha hb hc hx ht hs hbad with h|h
        · obtain ⟨hu,hv,hn⟩ := h
          obtain ⟨hdet,hcross⟩ := F.weighted_route a b c d (a+b) (c+d) ha hc hd hx hu hv hn
          exact ⟨3,G.table_positive_nonsingular _ _ _ _ (mul_ne_zero ha hu) (mul_ne_zero hc hu) hdet hcross⟩
        · obtain ⟨hu,hv,hn⟩ := h
          obtain ⟨hdet,hcross⟩ := F.weighted_route a b c d (a+c) (b+d) ha hc hd hx hu hv hn
          exact ⟨4,G.table_positive_nonsingular _ _ _ _ (mul_ne_zero ha hu) (mul_ne_zero hc hu) hdet hcross⟩
      · exact ⟨2,G.square_route a b c d ha hc hd hx hs⟩
    · have hdt : G.determinant a c b d≠0 := by simpa only [G.determinant,mul_comm c b] using hd
      exact ⟨1,G.table_positive_nonsingular a c b d ha hb hdt ht⟩
  · exact ⟨0,G.table_positive_nonsingular a b c d ha hc hd hx⟩

/-- Choice is from five explicit original coefficient formulas. -/
def choice (a b c d : ℂ) : Fin 5 :=
  if G.cross a b c d≠0 then 0 else
  if G.cross a c b d≠0 then 1 else
  if a*d+b*c≠0 then 2 else
  if a^4≠b^4 then 3 else 4

theorem choice_good (a b c d : ℂ) (ha : a≠0) (hb : b≠0) (hc : c≠0)
    (hd : G.determinant a b c d≠0) (he : ¬exceptional a b c d) :
    Good (candidate a b c d (choice a b c d)) := by
  unfold choice
  split_ifs with hx ht hs hab
  · exact G.table_positive_nonsingular a b c d ha hc hd hx
  · have hdt : G.determinant a c b d≠0 := by simpa only [G.determinant,mul_comm c b] using hd
    exact G.table_positive_nonsingular a c b d ha hb hdt ht
  · exact G.square_route a b c d ha hc hd (not_ne_iff.mp hx) hs
  · obtain ⟨hu,hv,hn⟩ := EOBinaryPlaneFlat.row_sums_good a b c d ha hb hc
      (not_ne_iff.mp hx) (not_ne_iff.mp ht) (not_ne_iff.mp hs) hab
    obtain ⟨hdet,hcross⟩ := F.weighted_route a b c d (a+b) (c+d) ha hc hd
      (not_ne_iff.mp hx) hu hv hn
    exact G.table_positive_nonsingular _ _ _ _ (mul_ne_zero ha hu) (mul_ne_zero hc hu) hdet hcross
  · have hbad : a^4≠b^4 ∨ a^4≠c^4 ∨ a^4≠d^4 := by
      by_contra hn
      push Not at hn
      exact he ⟨hn.1,hn.2.1,hn.2.2,eq_neg_of_add_eq_zero_left (not_ne_iff.mp hs)⟩
    have hac : a^4≠c^4 := by
      intro hac
      have had : a*d= -(b*c) := eq_neg_of_add_eq_zero_left (not_ne_iff.mp hs)
      have hp := congrArg (fun z : ℂ=>z^4) had
      have hn : (-(b*c))^4=b^4*c^4 := by ring
      rw [mul_pow,hn,←not_ne_iff.mp hab,←hac] at hp
      have had4 : a^4=d^4 := (mul_left_cancel₀ (pow_ne_zero 4 ha) hp).symm
      rcases hbad with h|h|h
      · exact h (not_ne_iff.mp hab)
      · exact h hac
      · exact h had4
    obtain ⟨hu,hv,hn⟩ := EOBinaryPlaneFlat.row_sums_good a c b d ha hc hb
      (not_ne_iff.mp ht) (not_ne_iff.mp hx) (by simpa only [mul_comm c b] using not_ne_iff.mp hs) hac
    obtain ⟨hdet,hcross⟩ := F.weighted_route a b c d (a+c) (b+d) ha hc hd
      (not_ne_iff.mp hx) hu hv hn
    exact G.table_positive_nonsingular _ _ _ _ (mul_ne_zero ha hu) (mul_ne_zero hc hu) hdet hcross

namespace B
export EOBinaryPlaneClassification (Full full_product_iff full_affine_iff Cross SignedCross CommonFourth)
end B

def a (f : Signature AlgebraicComplex 2) : ℂ := f ![false,false]
def b (f : Signature AlgebraicComplex 2) : ℂ := f ![false,true]
def c (f : Signature AlgebraicComplex 2) : ℂ := f ![true,false]
def d (f : Signature AlgebraicComplex 2) : ℂ := f ![true,true]

theorem exceptional_affine (f : Signature AlgebraicComplex 2) (hf : B.Full f)
    (h : exceptional (a f) (b f) (c f) (d f)) : Holant.Tractable.Affine f := by
  apply (B.full_affine_iff f hf).mpr
  have hab : f ![false,false]^4=f ![false,true]^4 := Subtype.ext h.1
  have hac : f ![false,false]^4=f ![true,false]^4 := Subtype.ext h.2.1
  have had : f ![false,false]^4=f ![true,true]^4 := Subtype.ext h.2.2.1
  constructor
  · intro z
    have hz : z=![z 0,z 1] := by funext i; fin_cases i <;> rfl
    rw [hz]
    cases z 0 <;> cases z 1
    · rfl
    · exact hab.symm
    · exact hac.symm
    · exact had.symm
  · exact Or.inr (Subtype.ext h.2.2.2)

/-- Literal EOTract failure on a full plane feeds the finite coefficient
producer; the output is a positive nonsingular table, not a hardness premise. -/
theorem nontract_positive (f : Signature AlgebraicComplex 2) (hf : B.Full f)
    (hn : ¬Holant.Tractable.EOTract {⟨4,EOBinaryPlaneCore.lift f⟩}) :
    Good (candidate (a f) (b f) (c f) (d f) (choice (a f) (b f) (c f) (d f))) := by
  have hna : ¬Holant.Tractable.Affine f := fun h=>hn (EOBinaryPlaneTract.lift_tract_iff f |>.mpr (Or.inl h))
  have hnp : ¬Holant.Tractable.Product f := fun h=>hn (EOBinaryPlaneTract.lift_tract_iff f |>.mpr (Or.inr h))
  have ha : a f≠0 := by simpa [a] using hf ![false,false]
  have hb : b f≠0 := by simpa [b] using hf ![false,true]
  have hc : c f≠0 := by simpa [c] using hf ![true,false]
  apply choice_good _ _ _ _ ha hb hc
  · intro hd
    apply hnp
    apply (B.full_product_iff f hf).mpr
    exact Subtype.ext (sub_eq_zero.mp hd)
  · exact fun he=>hna (exceptional_affine f hf he)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlanePositive
