import Holant.Proofs.Closure.ClosureExoticFiberTwo

/-! With two untouched nonconstant coordinates, a genuine safe four-row cross
output forces the fused coordinate constant. This uses exact proper output safety. -/
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureExoticFiberCounts
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Holant Holant.Pauli.ExoticKlein
open Holant.Certificates.MatchingContractionClosure
variable {P : Type*} [Fintype P] [LinearOrder P] {r : ℕ}

private theorem third_constant {J : Type*} (labels : Label → J → Label)
    (u v z : J) (huv : u≠v) (hzu : z≠u) (hzv : z≠v)
    (hu : Function.Injective (fun a => labels a u))
    (hv : Function.Injective (fun a => labels a v))
    (bound : ∃ p q : J,p≠q ∧ ∀ a b : Label,∀ j,j≠p → j≠q → labels a j=labels b j) :
    ∀ a b,labels a z=labels b z := by
  classical
  obtain ⟨p,q,hpq,outside⟩ := bound
  have inside (j : J) (hi : Function.Injective (fun a => labels a j)) : j=p ∨ j=q := by
    by_cases hp : j=p
    · exact Or.inl hp
    by_cases hq : j=q
    · exact Or.inr hq
    have he := hi (outside (0 : Label) xLabel j hp hq)
    exact False.elim ((by decide : (0 : Label)≠xLabel) he)
  have iu := inside u hu
  have iv := inside v hv
  intro a b
  rcases iu with up | uq <;> rcases iv with vp | vq
  · exact False.elim (huv (up.trans vp.symm))
  · exact outside a b z (fun hz => hzu (hz.trans up.symm)) (fun hz => hzv (hz.trans vq.symm))
  · exact outside a b z (fun hz => hzv (hz.trans vp.symm)) (fun hz => hzu (hz.trans uq.symm))
  · exact False.elim (huv (uq.trans vq.symm))

/-- A cross between e/f leaves the distinct u/v edges untouched. If their
label maps are injective and all rows live, the literal fused sum is constant. -/
theorem cross_sum_constant (M : Matching P r) (weight : Label → ℂ)
    (labels : Label → Fin r → Label) (u v e f : Fin r)
    (huv : u≠v) (hue : u≠e) (huf : u≠f) (hve : v≠e) (hvf : v≠f) (hef : e≠f)
    (hlabel : ∀ a,labels a u=a) (live : ∀ a,weight a≠0)
    (hinj : Function.Injective (fun a => labels a v))
    (hs : MatchingCard.PairSafe (Fiber.tensor M weight labels)) :
    ∀ a b,labels a e+labels a f=labels b e+labels b f := by
  classical
  have huv' : M.ports (e,true)≠M.ports (f,false) := by
    intro h
    exact hef (congrArg Prod.fst (M.ports.injective h))
  have safe := hs _ _ huv' (0 : Label)
  rw [contract_fiber_cross M weight labels e f hef] at safe
  let ju := (edgeEnum f).symm ⟨u,huf⟩
  let jv := (edgeEnum f).symm ⟨v,hvf⟩
  let je := (edgeEnum f).symm ⟨e,hef⟩
  have huLabel (a : Label) : crossLabels labels e f 0 a ju=a := by
    simp only [crossLabels,ju,Equiv.apply_symm_apply,crossLabel,hue,ite_false,hlabel]
  have hvLabel (a : Label) : crossLabels labels e f 0 a jv=labels a v := by
    simp only [crossLabels,jv,Equiv.apply_symm_apply,crossLabel,hve,ite_false]
  have heLabel (a : Label) : crossLabels labels e f 0 a je=labels a e+labels a f := by
    simp only [crossLabels,je,Equiv.apply_symm_apply,crossLabel,ite_true,
      MatchingCard.spliceLabel,theta_zero,add_zero]
  have neq (x y : OtherEdges f) (hxy : x.val≠y.val) :
      (edgeEnum f).symm x≠(edgeEnum f).symm y := by
    intro h
    exact hxy (congrArg Subtype.val ((edgeEnum f).symm.injective h))
  have bound := safe_four_rows_only_two (crossed M e f)
    (crossWeight weight labels e f 0) (crossLabels labels e f 0) ju huLabel
    (fun a => (crossWeight_ne_zero weight labels e f 0 a).mpr (live a)) safe
  have constant := third_constant (crossLabels labels e f 0) ju jv je
    (neq _ _ huv) (neq _ _ (Ne.symm hue)) (neq _ _ (Ne.symm hve))
    (fun a b h => by simpa only [huLabel] using h)
    (fun a b h => hinj (by simpa only [hvLabel] using h)) bound
  intro a b
  simpa only [heLabel] using constant a b

end
end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureExoticFiberCounts
