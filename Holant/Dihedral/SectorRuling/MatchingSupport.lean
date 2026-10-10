import Holant.Dihedral.SectorRuling.RootGrid

/-! The affine support, exact 2^s cardinality and finite-root coefficient ratios
are all derived from the actual full current-group matching products. -/
noncomputable section
namespace Holant.Dihedral.SectorRuling
open Holant Holant.Marked Holant.Dihedral.CompatibleClosure Holant.Certificates
open Holant.Dihedral.EndpointParallelogram Holant.Dihedral.TwoCardLocalization
set_option backward.isDefEq.respectTransparency false

def MatchingSample (m s : ℕ) (q : Signature Scalar (2*s)) : Prop :=
  ∃ p : (Fin s × Bool) ≃ Fin (2*s), ∃ A : Fin s → Mat, ∃ κ : Scalar,
    (∀ e,A e ∈ groupM m) ∧ κ ≠ 0 ∧ q=MatchingContractionClosure.productValue p A κ

def coefficients {n : ℕ} (q : Signature Scalar n) : (Fin n → ZMod 2) → Scalar :=
  fun x => q ((bitsEquiv (Fin n)).symm x)

/-- Every ratio is between actual nonzero entries, with the original matrix
scalar cancelled explicitly. -/
theorem binary_ratio_root {m : ℕ} (hm : 0<m) (A : Mat) (hA : A ∈ groupM m)
    (a b c d : Bool) (hab : A a b ≠ 0) (hcd : A c d ≠ 0) : Roots m (A a b/A c d) := by
  obtain ⟨α,z,k,hz,hk,rfl⟩ := group_M_normal_form hm hA
  have hb : b=(a ^^ α) := by
    by_contra h
    simp [Marked.scale,M,monomial,h] at hab
  have hd : d=(c ^^ α) := by
    by_contra h
    simp [Marked.scale,M,monomial,h] at hcd
  have he : scale k (M α z) a b/scale k (M α z) c d=
      (if a then z else 1)/(if c then z else 1) := by
    simp only [Marked.scale,M,monomial,hb,hd,ite_true]
    field_simp [hk]
  rw [he]
  apply Roots.div
  · cases a
    · exact Roots.one m
    · exact hz
  · cases c
    · exact Roots.one m
    · exact hz

theorem product_ratio_root {m s n : ℕ} (hm : 0<m) (p : (Fin s × Bool) ≃ Fin n)
    (A : Fin s → Mat) (κ : Scalar) (hA : ∀ e,A e ∈ groupM m) (hκ : κ ≠ 0)
    (x y : Fin n → Bool)
    (hx : MatchingContractionClosure.productValue p A κ x ≠ 0)
    (hy : MatchingContractionClosure.productValue p A κ y ≠ 0) :
    Roots m (MatchingContractionClosure.productValue p A κ x/MatchingContractionClosure.productValue p A κ y) := by
  classical
  have hx' e := (Finset.prod_ne_zero_iff.mp (mul_ne_zero_iff.mp hx).2) e (Finset.mem_univ e)
  have hy' e := (Finset.prod_ne_zero_iff.mp (mul_ne_zero_iff.mp hy).2) e (Finset.mem_univ e)
  let r := fun e => A e (x (p (e,false))) (x (p (e,true)))/A e (y (p (e,false))) (y (p (e,true)))
  have hr e : Roots m (r e) := binary_ratio_root hm _ (hA e) _ _ _ _ (hx' e) (hy' e)
  have hp (S : Finset (Fin s)) : Roots m (∏ e ∈ S,r e) := by
    induction S using Finset.induction_on with
    | empty => simpa using Roots.one m
    | @insert e S he ih => rw [Finset.prod_insert he]; exact (hr e).mul ih
  have he : MatchingContractionClosure.productValue p A κ x/MatchingContractionClosure.productValue p A κ y = ∏ e,r e := by
    simp only [MatchingContractionClosure.productValue,r,Finset.prod_div_distrib]
    field_simp [hκ]
  rw [he]
  exact hp Finset.univ

def matchingWord {s n : ℕ} (p : (Fin s × Bool) ≃ Fin n) (α : Fin s → Bool) (z : Fin s → Bool) : Fin n → Bool :=
  fun i => if (p.symm i).2 then z (p.symm i).1 ^^ α (p.symm i).1 else z (p.symm i).1

/-- The matching support has exactly one freely chosen bit per original edge. -/
theorem product_support_card {s n : ℕ} (p : (Fin s × Bool) ≃ Fin n)
    (A : Fin s → Mat) (κ : Scalar) (hA : ∀ e,IsMonomial (A e)) (hκ : κ ≠ 0) :
    (support (coefficients (MatchingContractionClosure.productValue p A κ))).card=2^s := by
  classical
  choose α w hw he using hA
  have hp (x : Fin n → Bool) : MatchingContractionClosure.productValue p A κ x ≠ 0 ↔
      ∀ e,x (p (e,true))=(x (p (e,false)) ^^ α e) := by
    simp only [MatchingContractionClosure.productValue,mul_ne_zero_iff,hκ,true_and,
      Finset.prod_ne_zero_iff,Finset.mem_univ,forall_const]
    have hcoef (e : Fin s) : A e (x (p (e,false))) (x (p (e,true))) ≠ 0 ↔
        x (p (e,true))=(x (p (e,false)) ^^ α e) := by
      rw [he e]
      simp [monomial,hw]
    constructor
    · rintro ⟨_,hx⟩ e
      exact (hcoef e).mp (hx e)
    · intro hx
      exact ⟨hκ,fun e => (hcoef e).mpr (hx e)⟩
  let E : (Fin s → Bool) ≃ ↥(support (coefficients (MatchingContractionClosure.productValue p A κ))) := {
    toFun z := ⟨bitsEquiv (Fin n) (matchingWord p α z),by
      rw [mem_support]
      change MatchingContractionClosure.productValue p A κ
        ((bitsEquiv (Fin n)).symm (bitsEquiv (Fin n) (matchingWord p α z))) ≠ 0
      rw [Equiv.symm_apply_apply,hp]
      intro e
      simp [matchingWord]⟩
    invFun x := fun e => (bitsEquiv (Fin n)).symm x.val (p (e,false))
    left_inv z := by funext e; simp [matchingWord]
    right_inv x := by
      apply Subtype.ext
      apply (bitsEquiv (Fin n)).symm.injective
      rw [Equiv.symm_apply_apply]
      have hxnon : coefficients (MatchingContractionClosure.productValue p A κ) x.val ≠ 0 :=
        (mem_support _ x.val).mp x.property
      have hx := (hp ((bitsEquiv (Fin n)).symm x.val)).mp hxnon
      funext i
      obtain ⟨⟨e,b⟩,rfl⟩ := p.surjective i
      cases b
      · simp [matchingWord]
      · simpa [matchingWord] using (hx e).symm }
  have hc := Fintype.card_congr E
  simpa only [Fintype.card_coe,Fintype.card_fun,Fintype.card_fin,Fintype.card_bool] using hc.symm

/-- All support/count/ratio inputs of the finite-pencil rigidity theorem are
proved from an actual sampled matching product. -/
theorem matching_sample_info {m s : ℕ} (hm : 0<m) (q : Signature Scalar (2*s)) (hq : MatchingSample m s q) :
    SampleInfo m (2^s) (coefficients q) := by
  obtain ⟨p,A,κ,hA,hκ,rfl⟩ := hq
  have hmono e := groupM_isMonomial hm (hA e)
  obtain ⟨a,ha⟩ := product_cardMatching p A κ hmono hκ
  refine ⟨affineClosed_of_coset _ (Pairing.ofPorts p).code a (fun x => ?_),product_support_card p A κ hmono hκ,?_⟩
  · exact (mem_support _ _).trans (ha x)
  · intro x y hx hy
    exact product_ratio_root hm p A κ hA hκ _ _ hx hy

end Holant.Dihedral.SectorRuling
