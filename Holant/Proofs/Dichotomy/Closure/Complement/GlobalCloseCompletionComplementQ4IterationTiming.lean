import Holant.Proofs.Dichotomy.Closure.Complement.GlobalCloseCompletionComplementQ4IterationBounds

/-! Polynomial retiming of the exact outer controller. Its width polynomial
is constructed from the proved arithmetic budgets, and the cell timing is
the actual fixed-field pass implementation. No loop-time callback is used. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4IterationTiming
open Holant Holant.Algebraic Holant.Complexity Holant.OneHot
open BinaryCompose FixedFieldMachines GraphPreprocessing
open Holant.LocalDrafts.RemoteWork.RationalLP.Support.Infrastructure
namespace I
export GlobalCloseCompletionComplementQ4IterationMachine (stateEncoding cell finite step)
end I
namespace B
export GlobalCloseCompletionComplementQ4IterationBounds (width stored_bound)
end B
namespace R
export Holant.LocalDrafts.RemoteWork.RationalLP.Support.Infrastructure.ReverseFold
  (inputEncoding encoding tailEncoding start step)
end R
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K A : Type} [Field K] [Algebra ℚ K] [Fintype A] {degree : ℕ}
variable (F : FixedField K degree) (coeff : A→Fin degree→ℚ)

def widthPolynomial (d l r y t e : Polynomial ℕ) : Polynomial ℕ:=
  let bytes:=Holant.Complexity.BinaryInterpolation.RingFormulaMachine.widthPolynomial F coeff
  2*((2*bytes.comp r+2)*d+1)+2*d+
  2*((2*bytes.comp (y+d*(r+2))+2)*l+1)+2*bytes.comp t+bytes.comp (e+d*(t+r+2))+4

theorem width_eval (d l r y t e : Polynomial ℕ) (n : ℕ) :
    (widthPolynomial F coeff d l r y t e).eval n=
      B.width F coeff (d.eval n) (l.eval n) (r.eval n) (y.eval n) (t.eval n) (e.eval n) := by
  simp [widthPolynomial,B.width,Holant.Complexity.BinaryInterpolation.RingFormulaMachine.widthPolynomial,ArithmeticSize.bitBound]

def timePolynomial (d l r y t e : Polynomial ℕ) : Polynomial ℕ:=
  Fold.time F.encoding (I.stateEncoding F) (0:K) I.step (Timing.ofPoly (I.cell F))
    (widthPolynomial F coeff d l r y t e) (widthPolynomial F coeff d l r y t e)

variable (unit neg : A) (hone : F.decode (coeff unit)=1) (hneg : F.decode (coeff neg)= -1)

include hone hneg in
theorem steps (roots values : List K) (target denominator : K)
    (d l r y t e : Polynomial ℕ) (n : ℕ)
    (hd : roots.length≤d.eval n) (hl : values.length≤l.eval n)
    (hr : ∀x∈roots,ArithmeticSize.Bound (fun a=>F.decode (coeff a)) (r.eval n) x)
    (hv : ∀x∈values,ArithmeticSize.Bound (fun a=>F.decode (coeff a)) (y.eval n) x)
    (ht : ArithmeticSize.Bound (fun a=>F.decode (coeff a)) (t.eval n) target)
    (he : ArithmeticSize.Bound (fun a=>F.decode (coeff a)) (e.eval n) denominator) :
    ((I.finite F).outputs (roots,(values,(target,denominator)))).steps≤
      (timePolynomial F coeff d l r y t e).eval n := by
  let w:=widthPolynomial F coeff d l r y t e
  have stored (k : ℕ) : ((R.encoding F.encoding (I.stateEncoding F)).encode
      (((R.step (0:K) I.step)^[k]) (R.start (roots,(values,(target,denominator)))))).length≤w.eval n := by
    rw [width_eval]
    exact B.stored_bound F coeff unit neg hone hneg roots values target denominator
      _ _ _ _ _ _ hd hl hr hv ht he k
  have initial : ((R.inputEncoding F.encoding (I.stateEncoding F)).encode
      (roots,(values,(target,denominator)))).length≤w.eval n := by
    have first:=stored 0
    simp only [Function.iterate_zero,Function.id_def,R.start,R.inputEncoding,R.encoding,R.tailEncoding,
      pairEncoding_length,UnaryBinary.unaryEncoding,List.length_replicate] at first ⊢
    omega
  exact Fold.steps F.encoding (I.stateEncoding F) (0:K) I.step (Timing.ofPoly (I.cell F))
    w w (roots,(values,(target,denominator))) n initial stored

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4IterationTiming
end
