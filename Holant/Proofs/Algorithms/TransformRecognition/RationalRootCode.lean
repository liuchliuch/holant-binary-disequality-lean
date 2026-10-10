import Holant.Proofs.AlgebraicRecognition.RootCode


namespace Holant.LocalDrafts.MainChain.TransformRecognition.RationalRootCode
open Holant.LocalDrafts.EffectiveAlgebraic Polynomial

def code (q : ℚ) : RootCode :=
  ⟨[(1,1),(0,-q)],⟨q-1,q+1,-1,1⟩⟩

theorem polynomial_code (q : ℚ) : (code q).polynomial=X-C q := by
  simp [code,RootCode.polynomial,RationalPolynomialCode.polynomial,Polynomial.X,
    sub_eq_add_neg]

theorem represents (q : ℚ) : (code q).Represents (q : ℂ) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro h
    have he := congrArg (fun p : ℚ[X] => p.coeff 1) h
    simp [polynomial_code] at he
  · norm_num [code,RationalRectangle.Contains]
  · simp [polynomial_code]
  · intro z _ hz
    have he : z-(q : ℂ)=0 := by simpa [polynomial_code] using hz
    exact sub_eq_zero.mp he

end Holant.LocalDrafts.MainChain.TransformRecognition.RationalRootCode
