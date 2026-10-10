import Holant.Certificates.EqualityQuaternary.KleinBasis

/-! All row/column cards force an actual partial injection of Bell labels.
It is extended to a permutation with zero coefficients on absent rows.
Thus 24 full permutations cover every one of the 209 partial supports.
-/
noncomputable section
namespace Holant.Certificates.EqualityQuaternary.Klein
open Holant Holant.Marked Holant.Tractable Holant.Marked.SupportAtlas
set_option backward.isDefEq.respectTransparency false

def card (kind : Kind) (q : Signature Scalar 4) (e : Equiv.Perm (Fin 4)) (a : Fin 4) : Mat :=
  contract0 (reorder q e) (dual kind a)
def AllDualCards (kind : Kind) (q : Signature Scalar 4) : Prop :=
  ∀ (e : Equiv.Perm (Fin 4)) (a : Fin 4),OnLine kind (card kind q e a)

theorem permute_refl (w : Fin 4 → Bool) : permuteWord (Equiv.refl _) w=w := rfl
theorem permute_swap (a b c d : Bool) : permuteWord swapBlocks ![a,b,c,d]=![c,d,a,b] := by
  funext i; fin_cases i <;> rfl
theorem permute_trans (p e : Equiv.Perm (Fin 4)) (w : Fin 4 → Bool) :
    permuteWord p (permuteWord e w)=permuteWord (e.trans p) w := rfl

theorem firstCard_eq_card (kind : Kind) (q : Signature Scalar 4) (a : Fin 4) :
    firstCard kind q a=card kind q (Equiv.refl _) a := by
  funext u v
  simp only [firstCard,card,contract0,reorder,permute_refl]

theorem tensorCoeff_swap (kind : Kind) (q : Signature Scalar 4) (a b : Fin 4) :
    tensorCoeff kind (reorder q swapBlocks) b a=tensorCoeff kind q a b := by
  simp only [tensorCoeff,coefficient,firstCard,Kernel.pair,Fintype.sum_bool,reorder,permute_swap]
  ring

theorem card_reorder (kind : Kind) (q : Signature Scalar 4) (p e : Equiv.Perm (Fin 4)) (a : Fin 4) :
    card kind (reorder q p) e a=card kind q (e.trans p) a := by
  funext u v
  simp only [card,contract0,reorder,permute_trans]

theorem AllDualCards.reorder {kind : Kind} {q : Signature Scalar 4}
    (h : AllDualCards kind q) (p : Equiv.Perm (Fin 4)) : AllDualCards kind (reorder q p) := by
  intro e a
  rw [card_reorder]
  exact h _ _

theorem row_unique {kind : Kind} {q : Signature Scalar 4} (h : AllDualCards kind q)
    (a b c : Fin 4) (hb : tensorCoeff kind q a b≠0) (hc : tensorCoeff kind q a c≠0) : b=c := by
  obtain ⟨k,hk⟩ := onLine_coefficients (h (Equiv.refl _) a)
  have hn (j : Fin 4) (hj : tensorCoeff kind q a j≠0) : j=k := by
    by_contra hne
    apply hj
    rw [tensorCoeff,firstCard_eq_card]
    exact hk j hne
  exact (hn b hb).trans (hn c hc).symm

theorem column_unique {kind : Kind} {q : Signature Scalar 4} (h : AllDualCards kind q)
    (a b c : Fin 4) (ha : tensorCoeff kind q a b≠0) (hc : tensorCoeff kind q c b≠0) : a=c := by
  exact row_unique (h.reorder swapBlocks) b a c
    (by rwa [tensorCoeff_swap]) (by rwa [tensorCoeff_swap])

theorem permutation_support {kind : Kind} {q : Signature Scalar 4} (h : AllDualCards kind q) :
    ∃ p : Equiv.Perm (Fin 4),∀ a b,tensorCoeff kind q a b≠0 → b=p a := by
  classical
  let Rows := {a : Fin 4 // ∃ b,tensorCoeff kind q a b≠0}
  let f : Rows → Fin 4 := Subtype.val
  let g : Rows → Fin 4 := fun a => Classical.choose a.property
  have hg (a : Rows) : tensorCoeff kind q a.val (g a)≠0 := Classical.choose_spec a.property
  have hg_inj : Function.Injective g := by
    intro a b hab
    apply Subtype.ext
    apply column_unique h a.val (g a) b.val (hg a)
    simpa only [hab] using hg b
  obtain ⟨p,hp⟩ := Equiv.Perm.exists_extending_pair f g Subtype.val_injective hg_inj
  refine ⟨p,?_⟩
  intro a b hab
  let r : Rows := ⟨a,⟨b,hab⟩⟩
  have he := row_unique h a b (g r) hab (hg r)
  exact he.trans (hp r).symm

def normalized (kind : Kind) (p : Equiv.Perm (Fin 4)) (c : Fin 4 → Scalar) : Signature Scalar 4 :=
  fun w => ∑ a : Fin 4,c a*basisTensor kind a (p a) w

/-- No coefficient is normalized to one; the four original algebraic scales,
including zero scales, remain free variables for the finite certificate. -/
theorem source_permutation_form {kind : Kind} {q : Signature Scalar 4} (h : AllDualCards kind q) :
    ∃ (p : Equiv.Perm (Fin 4)) (c : Fin 4 → Scalar),q=normalized kind p c := by
  obtain ⟨p,hp⟩ := permutation_support h
  refine ⟨p,fun a => tensorCoeff kind q a (p a),?_⟩
  funext w
  rw [←reconstruct_tensor kind q w]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_eq_single (p a)]
  · intro b _ hne
    have hz : tensorCoeff kind q a b=0 := by
      by_contra hn
      exact hne (hp a b hn)
    rw [hz,zero_mul]
  · simp

end Holant.Certificates.EqualityQuaternary.Klein
