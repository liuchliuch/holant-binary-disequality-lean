import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeSparseRankTwoThree
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeSparseMixingAlpha

/-! The residual nonaffine full binary phase is exactly the three-character
uniform-twisted Affine class. This is derived from the actual coefficient
classification and Affine square, never supplied as a residual class test. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeRankTwoAlphaCore
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open OrdinaryNegativeAffineSystematicSupport OrdinaryNegativeSparseRankDescent
open OrdinaryNegativeSparseMinimalRank
namespace B
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneClassification
  (Full CommonFourth Cross SignedCross affine_signed_cross full_affine_iff)
end B
namespace A
export OrdinaryNegativeSparseMixingAlpha (phaseThree phaseThree_formula twist_nonzero codeThree)
end A
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192

/-- Common fourth powers exclude the positive cross-square alternative for
an actual nonaffine full-support binary row. -/
theorem negative_cross_square (u : Signature AlgebraicComplex 2) (full : B.Full u)
    (square : Affine (fun x=>u x^2)) (fourth : B.CommonFourth u) (bad : ¬Affine u) :
    (u ![false,false]*u ![true,true])^2= -(u ![false,true]*u ![true,false])^2 := by
  have h := B.affine_signed_cross (fun x=>u x^2) (fun x=>pow_ne_zero 2 (full x)) square
  rcases h with positive|negative
  · have he : (u ![false,false]*u ![true,true])^2=(u ![false,true]*u ![true,false])^2 := by
      simpa only [B.Cross,mul_pow] using positive
    have hs : B.SignedCross u := sq_eq_sq_iff_eq_or_eq_neg.mp he
    exact False.elim (bad ((B.full_affine_iff u full).mpr ⟨fourth,hs⟩))
  · simpa only [mul_pow] using negative

theorem phaseThree_fourth (x : Fin 2→Bool) : A.phaseThree x^4=1 := by
  rw [A.phaseThree_formula]
  split_ifs <;> simp [imaginaryUnit_pow_four]

/-- Multiplying the actual residual binary by the three-character phase
produces an explicit literal Affine row. -/
theorem phaseThree_affine (u : Signature AlgebraicComplex 2) (full : B.Full u)
    (square : Affine (fun x=>u x^2)) (fourth : B.CommonFourth u) (bad : ¬Affine u) :
    Affine (fun x=>A.phaseThree x*u x) := by
  have hf : B.Full (fun x=>A.phaseThree x*u x) :=
    fun x=>mul_ne_zero (A.twist_nonzero (A.codeThree x)) (full x)
  apply (B.full_affine_iff _ hf).mpr
  constructor
  · intro x
    simp only [mul_pow,phaseThree_fourth,one_mul]
    exact fourth x
  · have negative := negative_cross_square u full square fourth bad
    apply sq_eq_sq_iff_eq_or_eq_neg.mp
    simp only [A.phaseThree_formula,Bool.false_or,Bool.true_or,Bool.false_eq_true,ite_true,ite_false,
      Matrix.cons_val_zero,Matrix.cons_val_one,one_mul]
    calc
      (u ![false,false]*(imaginaryUnit*u ![true,true]))^2=
        imaginaryUnit^2*(u ![false,false]*u ![true,true])^2 := by ring
      _= -(u ![false,false]*u ![true,true])^2 := by rw [imaginaryUnit_sq];ring
      _= (u ![false,true]*u ![true,false])^2 := by rw [negative];ring
      _= ((imaginaryUnit*u ![false,true])*(imaginaryUnit*u ![true,false]))^2 := by
        simp only [mul_pow,imaginaryUnit_sq]
        ring

variable {n : ℕ} {f : Signature AlgebraicComplex n} (D : SystematicSupport f 2)

/-- Proper-face minimality itself forces all four reduced fourth powers to
agree. Coordinate edges are connected through their actual outside settings. -/
theorem minimal_commonFourth
    (minimal : ∀S : Finset (Fin 2),S.card<2 → ∀z : Word 2,Affine (minor D S z)) :
    B.CommonFourth D.reduced := by
  intro x
  apply Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionFullSupport.constant_of_coordinates
    2 (fun z=>D.reduced z^4) _ x ![false,false]
  intro i z
  have ha := face_affine_of_minor D {i} z (minimal {i} (by simp) z)
  have value (b : Bool) : OrdinaryNegativeAffineThreeFaces.face D.reduced {i} z
      (Function.update z i b)=D.reduced (Function.update z i b) := by
    apply ite_eq_left
    intro j hj
    have hji : j≠i := by simpa using hj
    simp [Function.update,hji]
  have h0 : OrdinaryNegativeAffineThreeFaces.face D.reduced {i} z (Function.update z i false)≠0 := by
    rw [value];exact D.reduced_full _
  have h1 : OrdinaryNegativeAffineThreeFaces.face D.reduced {i} z (Function.update z i true)≠0 := by
    rw [value];exact D.reduced_full _
  have equal := ha.fourth_power_eq _ _ h0 h1
  simpa only [value] using equal

/-- Minimality supplies the common-fourth premise internally. -/
theorem minimal_phaseThree_affine (square : Affine (fun x=>f x^2)) (nonzero : f≠0)
    (bad : ¬Affine f)
    (minimal : ∀S : Finset (Fin 2),S.card<2 → ∀z : Word 2,Affine (minor D S z)) :
    Affine (fun x=>A.phaseThree x*D.reduced x) :=
  phaseThree_affine D.reduced D.reduced_full (square.precompose D.encode D.affine)
    (minimal_commonFourth D minimal) (D.nonAffine_reduced square nonzero bad)

/-- The actual systematic reduced row inherits the residual alpha class
from the original row's Affine square and supported fourth powers. -/
theorem reduced_phaseThree_affine (square : Affine (fun x=>f x^2)) (nonzero : f≠0)
    (fourth : OrdinaryNegativeFourthCompatibility.CommonFourth f) (bad : ¬Affine f) :
    Affine (fun x=>A.phaseThree x*D.reduced x) := by
  apply phaseThree_affine D.reduced D.reduced_full
    (square.precompose D.encode D.affine)
  · intro x
    exact fourth _ _ (D.supported x) (D.supported _)
  · exact D.nonAffine_reduced square nonzero bad

/-- The complementary uniform-class witness has the same explicit
residual classification, with all pin scalars accounted for. -/
theorem uniform_minimal_phaseThree_affine (square : Affine (fun x=>f x^2))
    (bad : ¬Affine (OrdinaryNegativeAffineRankOne.uniform f))
    (minimal : ∀S : Finset (Fin 2),S.card<2 → ∀z : Word 2,
      Affine (OrdinaryNegativeAffineRankOne.uniform (minor D S z))) :
    Affine (fun x=>A.phaseThree x*OrdinaryNegativeAffineRankOne.uniform f (D.encode x)) := by
  let E := OrdinaryNegativeSparseUniformMinimal.uniformChart D
  have hn : OrdinaryNegativeAffineRankOne.uniform f≠0 := by
    intro hz
    exact E.supported (origin 2) (congrFun hz _)
  exact minimal_phaseThree_affine E (OrdinaryNegativeAffineRankOne.uniform_square f square) hn bad
    (fun S hS z=>(OrdinaryNegativeSparseUniformMinimal.uniform_minor_affine_iff D S z).mpr (minimal S hS z))


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeRankTwoAlphaCore
end
