import Holant.EightVertex.ProductAnchor.GeneralizedEquality

namespace Holant.EightVertex.ProductAnchor
open Holant.Tractable
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem monomial_pair_support (T : Mat) (hT : Monomial T) (A B : Scalar) (s x : Word4)
    (hx : x≠s) (hy : x≠complementWord s) :
    Signature.coordinateAction (fun _ => T) (ge4 A B s) x=0 := by
  rcases hT with hT | hT
  · have he : T=diagonalKernel (T false false) (T true true) := by
      funext a b
      cases a <;> cases b <;> simp [diagonalKernel,hT.1,hT.2]
    rw [he,coordinateAction_diagonal]
    simp [ge4,hx,hy]
  · have he : T=Kernel.mul (diagonalKernel (T false true) (T true false)) Signature.disequality := by
      funext a b
      cases a <;> cases b <;> simp [Kernel.mul_apply,diagonalKernel,Signature.disequality,hT.1,hT.2]
    have hc0 : complementWord x≠s := by
      intro h
      apply hy
      simpa using congrArg complementWord h
    have hc1 : complementWord x≠complementWord s := by
      intro h
      apply hx
      simpa using congrArg complementWord h
    rw [he,coordinateAction_antidiagonal]
    simp [ge4,hc0,hc1]

theorem pure_of_pair_support (q : Signature Scalar 4) (s : Word4)
    (h0 : q (fun _ => false)≠0) (h1 : q (fun _ => true)≠0)
    (hs : ∀ x,x≠s → x≠complementWord s → q x=0) : PureEquality q := by
  have hword : s=(fun _ => false) ∨ s=(fun _ => true) := by
    by_cases h : s=(fun _ => false)
    · exact Or.inl h
    · right
      have H : (fun _ => false)=complementWord s := by
        by_contra hn
        exact h0 (hs _ (Ne.symm h) hn)
      have HH := congrArg complementWord H
      simpa [complementWord] using HH.symm
  refine ⟨q (fun _ => false),q (fun _ => true),h0,h1,?_⟩
  apply of_complement_support q (fun _ => false)
  intro x hx hy
  rcases hword with rfl | rfl
  · exact hs x hx hy
  · apply hs x
    · simpa [complementWord] using hy
    · simpa [complementWord] using hx

theorem monomial_ge_pure (T : Mat) (hT : Monomial T) (A B : Scalar) (s : Word4)
    (he : EndpointEven (Signature.coordinateAction (fun _ => T) (ge4 A B s))) :
    PureEquality (Signature.coordinateAction (fun _ => T) (ge4 A B s)) :=
  pure_of_pair_support _ s he.1 he.2.1 (monomial_pair_support T hT A B s)

theorem PureEquality.support_card {q : Signature Scalar 4} (h : PureEquality q) :
    ((Finset.univ : Finset Word4).filter fun x => q x≠0).card=2 := by
  obtain ⟨A,B,hA,hB,rfl⟩ := h
  have he : ((Finset.univ : Finset Word4).filter fun x => ge4 A B (fun _ => false) x≠0)=
      {(fun _ => false),(fun _ => true)} := by
    ext x
    by_cases h0 : x=(fun _ => false)
    · subst x; simp [hA,ge4,complementWord]
    by_cases h1 : x=(fun _ => true)
    · subst x; simp [hB,ge4,complementWord]
    simp [ge4,h0,h1,complementWord]
  rw [he]
  decide

end
end Holant.EightVertex.ProductAnchor
