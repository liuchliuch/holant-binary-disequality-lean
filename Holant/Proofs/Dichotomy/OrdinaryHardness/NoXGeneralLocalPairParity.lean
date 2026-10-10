import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXLocalRankOneWeighted
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralRankTwoFaces

/-! Two supported words of a row that is both Affine and LocalAffine have
even negative incidence in each order. The rank-two line counts are exact
counts of these physical incidences, including all original port signs. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralLocalPairParity
open Holant Holant.Tractable
open Holant.Tractable.SymmetricBinaryPullback
open OrdinaryNegativeAffineSystematicSupport
open OrdinaryNegativeSignedPortsCore (Port word)
namespace C
export NoXLocalRankOneCriterion (maskSign maskSign_square maskSign_pair twist_fourth twist_support)
export NoXLocalRankOneWeighted (signed_equation negativeSign_pow)
end C
namespace W
export NoXWeightedRankOneCore (negativeCount)
end W
namespace F
export NoXGeneralRankTwoFaces (line lineCount)
export OrdinaryNegativeRankTwoPorts (port word_code)
export OrdinaryNegativeSparseMixingAlpha (codeThree)
end F
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 32768
set_option Elab.async false

theorem even {n : ℕ} {f : Signature AlgebraicComplex n} (affine : Affine f) (localGood : LocalAffine f)
    (x y : Fin n→Bool) (hx : f x≠0) (hy : f y≠0) : Even (W.negativeCount x y) := by
  have phase:=(localGood x hx).fourth_power_eq x y
    ((C.twist_support f x x).mpr hx) ((C.twist_support f x y).mpr hy)
  simp only [C.twist_fourth] at phase
  have signed:=(C.signed_equation _ _ _ _ (C.maskSign_square x x)).mp phase
  rw [C.maskSign_pair,C.negativeSign_pow] at signed
  have same:=affine.fourth_power_eq x y hx hy
  have one : (-1 : AlgebraicComplex)^W.negativeCount x y=1:=by
    apply mul_right_cancel₀ (pow_ne_zero 4 hy)
    rw [one_mul,←signed,same]
  rcases Nat.even_or_odd (W.negativeCount x y) with he|ho
  · exact he
  · rw [ho.neg_one_pow] at one
    norm_num at one

theorem line_count {n : ℕ} (ps : Fin n→Port 3) (i : Fin 4) (reverse : Bool) :
    W.negativeCount (word ps (F.codeThree (F.line i reverse false)))
      (word ps (F.codeThree (F.line i reverse true)))=F.lineCount ps i (!reverse) := by
  fin_cases i <;> dsimp [F.lineCount]
  all_goals rw [W.negativeCount,NoXSeparateSignedProjection.signedCount,
    NoXSeparateSignedProjection.signedCount,←Finset.sum_add_distrib]
  all_goals apply Finset.sum_congr rfl
  all_goals intro k _
  all_goals cases hp : ps k with
    | inl b=>cases b <;> cases reverse <;>
        simp [word,F.codeThree,F.line,NoXGeneralRankTwoFaces.axis,NoXGeneralRankTwoFaces.outside,
          OrdinaryNegativeRankOneCore.neg,hp]
    | inr q=>
        rcases q with ⟨j,b⟩
        fin_cases j <;> cases b <;> cases reverse <;>
          simp [word,F.codeThree,F.line,NoXGeneralRankTwoFaces.axis,NoXGeneralRankTwoFaces.outside,
            OrdinaryNegativeRankOneCore.neg,hp]

theorem line_count_chart {n : ℕ} {f : Signature AlgebraicComplex n} (D : SystematicSupport f 2)
    (i : Fin 4) (reverse : Bool) :
    W.negativeCount (D.encode (F.line i reverse false)) (D.encode (F.line i reverse true))=
      F.lineCount (F.port D) i (!reverse) := by
  simpa only [F.word_code] using line_count (F.port D) i reverse

theorem uniform_parity {n : ℕ} (ps : Fin n→Port 3)
    (evenLines : ∀i bit,Even (F.lineCount ps i bit)) :
    (∀j bit,Even (NoXSeparateSignedProjection.signedCount ps j bit)) ∨
    (∀j bit,Odd (NoXSeparateSignedProjection.signedCount ps j bit)) := by
  have same : ∀j bit,Even (NoXSeparateSignedProjection.signedCount ps j bit) ↔
      Even (NoXSeparateSignedProjection.signedCount ps 2 false):=by
    intro j bit
    have h0:=(Nat.even_add.mp (evenLines 0 false))
    have h1:=(Nat.even_add.mp (evenLines 0 true))
    have h2:=(Nat.even_add.mp (evenLines 1 false))
    have h3:=(Nat.even_add.mp (evenLines 1 true))
    have h4:=(Nat.even_add.mp (evenLines 2 false))
    have h5:=(Nat.even_add.mp (evenLines 2 true))
    simp only [F.lineCount,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
      Matrix.cons_val_three,Matrix.head_cons,Bool.not_false,Bool.not_true] at h0 h1 h2 h3 h4 h5
    fin_cases j <;> cases bit
    · exact h0
    · exact h3
    · exact h4
    · exact h5.trans (h2.symm.trans h0)
    · rfl
    · exact h2.symm.trans h0
  rcases Nat.even_or_odd (NoXSeparateSignedProjection.signedCount ps 2 false) with he|ho
  · exact Or.inl (fun j bit=>(same j bit).mpr he)
  · exact Or.inr (fun j bit=>Nat.not_even_iff_odd.mp (fun h=>Nat.not_even_iff_odd.mpr ho ((same j bit).mp h)))


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralLocalPairParity
end
