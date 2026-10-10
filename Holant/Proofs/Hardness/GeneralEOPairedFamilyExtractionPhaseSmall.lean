import Holant.Proofs.Hardness.GeneralEOPairedFamilyExtractionPhaseNormalization

/-! The phase correction is identically one on every literal word of weight
zero, one or two. Higher phase obstructions can therefore be selected by the
proved minimal-support ternary extraction. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionPhaseSmall
open Holant Holant.Tractable
open GeneralEOPairedFamilyExtractionPhaseNormalization
open scoped BigOperators
namespace N
export GeneralEOPairedFamilyExtractionPhaseNormalization (residual)
end N
namespace A
export AffinePhase (word basis origin word_singleton word_empty)
end A
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false

variable {n : ℕ} (g : Signature AlgebraicComplex n) (h0 : g (A.origin n)=1)
variable (hfour : ∀x,g x^4=1)

include h0 in
theorem residual_empty : N.residual g (A.word ∅)=1 := by
  simp [N.residual,correction,unary,pair,A.word,h0]

theorem pair_single (e : Edge n) (i : Fin n) : pair g e (A.word {i})=1 := by
  have hn : ¬(e.val.1=i ∧ e.val.2=i) := by
    rintro ⟨ha,hb⟩
    have hh := e.property
    rw [ha,hb] at hh
    exact (lt_irrefl i) hh
  simp [pair,A.word,hn]

theorem unary_single_product (i : Fin n) :
    (∏j,unary g j (A.word {i})^3)=g (A.basis i)^3 := by
  have he (j : Fin n) : unary g j (A.word {i})^3=if j=i then g (A.basis i)^3 else 1 := by
    by_cases hj : j=i
    · subst j
      simp [unary,A.word]
    · simp [unary,A.word,hj]
  simp only [he,Finset.prod_ite_eq',Finset.mem_univ,ite_true]

include hfour in
theorem residual_single (i : Fin n) : N.residual g (A.word {i})=1 := by
  have hp : (∏e : Edge n,pair g e (A.word {i})^3)=1 := by
    apply Finset.prod_eq_one
    intro e _
    rw [pair_single,one_pow]
  rw [N.residual,correction,unary_single_product,hp,mul_one,A.word_singleton]
  calc
    _=g (A.basis i)^4 := by ring
    _=1 := hfour _

theorem pair_index_eq (a b : Fin n) (hab : a<b) (e : Edge n)
    (ha : e.val.1=a ∨ e.val.1=b) (hb : e.val.2=a ∨ e.val.2=b) : e=⟨(a,b),hab⟩ := by
  have he := e.property
  rcases ha with ha|ha <;> rcases hb with hb|hb
  · rw [ha,hb] at he
    exact False.elim ((lt_irrefl a) he)
  · exact Subtype.ext (Prod.ext ha hb)
  · rw [ha,hb] at he
    exact False.elim ((not_lt_of_gt hab) he)
  · rw [ha,hb] at he
    exact False.elim ((lt_irrefl b) he)

theorem pair_pair (a b : Fin n) (hab : a<b) (e : Edge n) :
    pair g e (A.word {a,b})=if e=⟨(a,b),hab⟩ then interaction g ⟨(a,b),hab⟩ else 1 := by
  by_cases he : e=⟨(a,b),hab⟩
  · subst e
    simp [pair,A.word]
  · rw [ite_eq_right he]
    have hn : ¬(e.val.1=a ∨ e.val.1=b) ∨ ¬(e.val.2=a ∨ e.val.2=b) := by
      by_contra hh
      push Not at hh
      exact he (pair_index_eq a b hab e hh.1 hh.2)
    rcases hn with hn|hn <;> simp [pair,A.word,hn]

theorem unary_pair_product (a b : Fin n) (hab : a≠b) :
    (∏j,unary g j (A.word {a,b})^3)=g (A.basis a)^3*g (A.basis b)^3 := by
  have he (j : Fin n) : unary g j (A.word {a,b})^3=
      (if j=a then g (A.basis a)^3 else 1)*(if j=b then g (A.basis b)^3 else 1) := by
    by_cases ha : j=a <;> by_cases hb : j=b
    · exact False.elim (hab (ha.symm.trans hb))
    · subst j
      simp [unary,A.word,hb]
    · subst j
      simp [unary,A.word,ha]
    · simp [unary,A.word,ha,hb]
  simp only [he,Finset.prod_mul_distrib,Finset.prod_ite_eq',Finset.mem_univ,ite_true]

include hfour in
theorem residual_pair (a b : Fin n) (hab : a<b) : N.residual g (A.word {a,b})=1 := by
  rw [N.residual,correction,unary_pair_product g a b (ne_of_lt hab)]
  have hp : (∏e : Edge n,pair g e (A.word {a,b})^3)=interaction g ⟨(a,b),hab⟩^3 := by
    simp only [pair_pair g a b hab,ite_pow,one_pow,Finset.prod_ite_eq',Finset.mem_univ,ite_true]
  rw [hp]
  calc
    _=interaction g ⟨(a,b),hab⟩^4 := by unfold interaction; ring
    _=1 := interaction_four g hfour _

include h0 hfour in
theorem residual_small (s : Finset (Fin n)) (hs : s.card≤2) : N.residual g (A.word s)=1 := by
  have hh : s.card=0 ∨ s.card=1 ∨ s.card=2 := by omega
  rcases hh with hh|hh|hh
  · have he := Finset.card_eq_zero.mp hh
    rw [he]
    exact residual_empty g h0
  · obtain ⟨i,rfl⟩ := Finset.card_eq_one.mp hh
    exact residual_single g hfour i
  · obtain ⟨a,b,hab,rfl⟩ := Finset.card_eq_two.mp hh
    rcases lt_or_gt_of_ne hab with h|h
    · exact residual_pair g hfour a b h
    · rw [Finset.pair_comm]
      exact residual_pair g hfour b a h

include h0 hfour in
/-- Every normalized nonaffine signature with affine literal pair tables has
an internally selected ternary monomial among its corrected restrictions. -/
theorem exists_ternary (ha : ¬Affine g) (hpair : ∀e : Edge n,Affine (pairTable g e)) :
    ∃p : Fin n → Bool ⊕ Fin 3,∃δ : AlgebraicComplex,δ^4=1 ∧ δ≠1 ∧
      ∀z : Fin 3 → Bool,N.residual g (GeneralEOPairedFamilyExtractionTensor.substitute p z)=
        if z=![true,true,true] then δ else 1 :=
  GeneralEOPairedFamilyExtractionPhaseMinor.exists_ternary_monomial (N.residual g)
    (residual_small g h0 hfour) (residual_nonconstant g hfour ha hpair) (residual_four g hfour)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionPhaseSmall
