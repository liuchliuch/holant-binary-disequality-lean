import Holant.EightVertex.ProductAnchor.TemplateTransport

/-! The literal manuscript equality-anchor predicate, including exact actual
realization, one algebraic basis, and both nonzero normalization scalars. -/
namespace Holant.EightVertex.ProductAnchor
open Holant.Tractable
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

 def HasEqualityAnchor (F : SignatureFamily Scalar) : Prop :=
  ∃ (g : Signature Scalar 4) (R : InvertibleKernel) (kappa lambda : Scalar),
    kappa≠0 ∧ lambda≠0 ∧ Gadget.Realizes F .disequality g ∧
    Kernel.pullback Signature.disequality R.inverse=(fun a b => kappa*Signature.equality a b) ∧
    R.action g=(fun x => lambda*equalityFour x)

 theorem coordinateAction_scale {K : Type*} [CommSemiring K] {n : ℕ}
    (A : Fin n → Kernel K) (c : K) (q : Signature K n) :
    Signature.coordinateAction A (fun x => c*q x)=
      fun x => c*Signature.coordinateAction A q x := by
  funext x
  simp only [Signature.coordinateAction,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ac_rfl

/-- A projectively realized physical template suffices because the equality
anchor definition itself retains its nonzero output scalar. -/
 theorem equality_anchor_of_template (F : SignatureFamily Scalar) (q : Signature Scalar 4)
    (R : InvertibleKernel) (s : Word4) (c : Scalar) (hc : c≠0)
    (hR : Kernel.pullback Signature.disequality R.inverse=Signature.equality)
    (htransport : R.action (anchorTemplate Signature.disequality s q)=fun x => c*equalityFour x)
    (hg : Gadget.RealizesUpTo F .disequality (anchorTemplate Signature.disequality s q)) :
    HasEqualityAnchor F := by
  obtain ⟨d,hd,hg⟩ := hg
  refine ⟨(fun x => d*anchorTemplate Signature.disequality s q x),R,1,d*c,
    one_ne_zero,mul_ne_zero hd hc,hg,?_,?_⟩
  · simpa using hR
  · change Signature.coordinateAction (fun _ => R.matrix)
      (fun x => d*anchorTemplate Signature.disequality s q x)=_
    rw [coordinateAction_scale]
    change (fun x => d*R.action (anchorTemplate Signature.disequality s q) x)=_
    rw [htransport]
    funext x
    ring

end
end Holant.EightVertex.ProductAnchor
