import Holant.Pauli.ExoticKlein.RulingProgram
import Holant.Pauli.ExoticKlein.RulingProductPair
import Holant.Dihedral.TwoCardLocalization.DistinctCore

/-! Fixed original-port rulings for exotic cards, source Lemma 8.6.
The actual distinct-matching localization program has positive length at
arity at least eight. Its first contraction is a proper card of the ancestor;
exotic closure therefore makes its terminal six-port tensor a matching
product. Its two preserved, different rulings give a contradiction. -/
namespace Holant.Pauli.ExoticKlein
noncomputable section
open scoped BigOperators
open Holant.Dihedral.TwoCardLocalization
open Holant.Certificates.MatchingContractionClosure
open Holant.Dihedral.CompatibleClosure
open Holant.Dihedral.CompatibleCoefficientLine

namespace MatchingCard

theorem product_front_fixed_matching {n r : ℕ} (M : Matching (Fin (n+2)) r)
    (labels : Fin r → Label) (weight : ℂ) (hw : weight ≠ 0) :
    ∃ s : ℕ, ∃ R : Matching (Fin n) s, ∀ a : Label,
      Signature.contract (dual a) (fun x => weight*M.tensor labels x) = 0 ∨
      ∃ fixed : Fin s → Label, ∃ c : ℂ, c ≠ 0 ∧
        Signature.contract (dual a) (fun x => weight*M.tensor labels x) = fun x => c*R.tensor fixed x := by
  obtain ⟨s,R,hR⟩ := product_pair_fixed_matching M labels weight hw 0 1 Fin.zero_ne_one
  let e := (remainingOrder (0 : Fin (n+2)) 1 Fin.zero_ne_one).symm
  refine ⟨s,⟨R.ports.trans e⟩,?_⟩
  intro a
  have he := contractPair_front (dual a) (fun x => weight*M.tensor labels x)
  rcases hR a with hz | ⟨fixed,c,hc,hh⟩
  · left
    rw [←he]
    exact congrArg (Tensor.reindex e) hz
  · right
    refine ⟨fixed,c,hc,?_⟩
    rw [←he]
    exact congrArg (Tensor.reindex e) hh

theorem exotic_not_different_front {n : ℕ} (q : Signature ℂ (n+2))
    (hq : ExoticMatchingOrZero q) (a b : Label) :
    ¬ DifferentProducts binaryGroup n (Signature.contract (dual a) q) (Signature.contract (dual b) q) := by
  intro hd
  have hn := hd.nonzero binaryGroup_projective
  rcases hq with rfl | ⟨r,M,labels,weight,hw,rfl⟩
  · apply hn.1
    funext x
    simp only [Signature.contract,Pi.zero_apply,mul_zero,Finset.sum_const_zero]
  · obtain ⟨s,R,hR⟩ := product_front_fixed_matching M labels weight hw
    obtain ⟨M₀,M₁,h₀,h₁,hs₀,hs₁,he₀,he₁,hne⟩ := hd
    obtain ⟨l₀,c₀,hc₀,hf₀⟩ := presentation_exotic_form M₀ h₀ hs₀
    obtain ⟨l₁,c₁,hc₁,hf₁⟩ := presentation_exotic_form M₁ h₁ hs₁
    rcases hR a with hz | ⟨lA,cA,hcA,hA⟩
    · exact hn.1 hz
    rcases hR b with hz | ⟨lB,cB,hcB,hB⟩
    · exact hn.2 hz
    have hA' := Matching.mate_eq_of_scaled_equality (presentationMatching M₀) R l₀ lA c₀ cA hc₀ hcA
      ((he₀.trans hf₀).symm.trans hA)
    have hB' := Matching.mate_eq_of_scaled_equality (presentationMatching M₁) R l₁ lB c₁ cB hc₁ hcB
      ((he₁.trans hf₁).symm.trans hB)
    exact hne (hA'.trans hB'.symm)

/-- Two original cards cannot carry different residual mate involutions.
The only extra contractions are actual copies of the fixed dual of E₀. -/
theorem no_different_cards (r : ℕ) (hr : 0 < r) (f : Signature ℂ (2*r+6))
    (hf : OrderedPairSafe f) (a b : Label) :
    ¬ DifferentProducts binaryGroup (2*r+4)
      (Signature.contract (dual a) f) (Signature.contract (dual b) f) := by
  intro hd
  obtain ⟨P,hP,hout⟩ := different_products_program binaryGroup binaryGroup_projective X_mem
    binaryGroup_reversal (dual 0) (dual_safe 0) r _ _ hd
  have hsafe := orderedPairSafe_core (fun _ : Unit => (0 : Label)) P (by omega) f hf
  apply exotic_not_different_front _ hsafe a b
  rwa [P.inherited_card,P.inherited_card]

theorem card_rulings_equal (r : ℕ) (hr : 0 < r) (f : Signature ℂ (2*r+6))
    (hf : OrderedPairSafe f) (a b : Label)
    {s t : ℕ} (M : Matching (Fin (2*r+4)) s) (N : Matching (Fin (2*r+4)) t)
    (labels : Fin s → Label) (fixed : Fin t → Label) (c d : ℂ) (hc : c ≠ 0) (hd : d ≠ 0)
    (hM : Signature.contract (dual a) f = fun x => c*M.tensor labels x)
    (hN : Signature.contract (dual b) f = fun x => d*N.tensor fixed x) : M.mate = N.mate := by
  by_contra hne
  apply no_different_cards r hr f hf a b
  exact ⟨⟨s,M.ports,fun e => asMatrix (E (labels e)),c⟩,
    ⟨t,N.ports,fun e => asMatrix (E (fixed e)),d⟩,
    fun e => E_safe _,fun e => E_safe _,hc,hd,hM,hN,hne⟩

theorem front_reconstruction {n : ℕ} (f : Signature ℂ (n+2)) (a b : Bool) (x : Fin n → Bool) :
    (∑ k : Label, Signature.contract (dual k) f x*E k a b) = f (pair a b x) :=
  binary_reconstruction (fun u v => f (pair u v x)) a b

theorem exists_nonzero_front_card {n : ℕ} (f : Signature ℂ (n+2)) (hf : f ≠ 0) :
    ∃ a : Label, Signature.contract (dual a) f ≠ 0 := by
  by_contra hn
  push_neg at hn
  apply hf
  funext x
  let z : Fin n → Bool := fun i => x i.succ.succ
  have hx : pair (x 0) (x 1) z = x := by
    funext i
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i <;> rfl
  have he := front_reconstruction f (x 0) (x 1) z
  rw [hx] at he
  simpa only [hn,Pi.zero_apply,zero_mul,Finset.sum_const_zero] using he.symm

/-- Full fixed-ruling conclusion at an arbitrary ordered deleted pair. The
chosen matching is shared by every nonzero card, independently of the card's
edge enumeration, edge orientation, labels and nonzero scale. -/
theorem fixed_ruling (r : ℕ) (hr : 0 < r) (f : Signature ℂ (2*r+6))
    (hf : f ≠ 0) (hs : OrderedPairSafe f) (p : Equiv.Perm (Fin (2*r+6))) :
    ∃ s : ℕ, ∃ M : Matching (Fin (2*r+4)) s,
      ∀ a : Label, ∀ t : ℕ, ∀ N : Matching (Fin (2*r+4)) t,
        ∀ labels : Fin t → Label, ∀ c : ℂ, c ≠ 0 →
        Signature.contract (dual a) (Tensor.reindex p.symm f) = (fun x => c*N.tensor labels x) →
        N.mate = M.mate := by
  let q := Tensor.reindex p.symm f
  have hq : q ≠ 0 := by
    intro hz
    apply hf
    funext x
    have hh := congrFun hz (fun i => x (p i))
    simpa only [q,Tensor.reindex,Equiv.apply_symm_apply,Pi.zero_apply] using hh
  obtain ⟨a,ha⟩ := exists_nonzero_front_card q hq
  have hsafe := orderedPairSafe_reindex f hs p
  have hcard : ExoticMatchingOrZero (Signature.contract (dual a) q) := hsafe (Equiv.refl _) a
  rcases hcard with hz | ⟨s,M,labels,c,hc,hM⟩
  · exact False.elim (ha hz)
  refine ⟨s,M,?_⟩
  intro b t N fixed d hd hN
  exact card_rulings_equal r hr q hsafe b a N M fixed labels d c hd hc hN hM

end MatchingCard
end
end Holant.Pauli.ExoticKlein
