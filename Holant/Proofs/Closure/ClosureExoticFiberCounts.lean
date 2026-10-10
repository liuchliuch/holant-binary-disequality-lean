import Holant.Pauli.ExoticKlein.FiberFactor

/-! Literal proper edge cards of the common exotic fibre. All support counts
below are applied to actual pair-safe OUTPUTS, never assumed for the ancestor. -/
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureExoticFiberCounts
noncomputable section
open scoped BigOperators
open Holant.Pauli.ExoticKlein
open Holant.Certificates.MatchingContractionClosure

variable {P : Type*} [Fintype P] [LinearOrder P] {r : ℕ}

def edgeEnum (e : Fin r) : Fin (Fintype.card (OtherEdges e)) ≃ OtherEdges e :=
  (Fintype.equivFin (OtherEdges e)).symm

def deleted (M : Matching P r) (e : Fin r) :
    Matching (Remaining (M.ports (e,false)) (M.ports (e,true)))
      (Fintype.card (OtherEdges e)) :=
  ⟨(Equiv.prodCongr (edgeEnum e) (Equiv.refl Bool)).trans (deletePorts M.ports e)⟩

def labelsAfter (labels : Label → Fin r → Label) (e : Fin r)
    (a : Label) (j : Fin (Fintype.card (OtherEdges e))) : Label :=
  labels a ((edgeEnum e) j).val

def weightAfter (weight : Label → ℂ) (labels : Label → Fin r → Label)
    (e : Fin r) (b a : Label) : ℂ := if labels a e = b then weight a else 0

theorem product_deleted (M : Matching P r) (labels : Fin r → Label) (e : Fin r)
    (c : ℂ) :
    productValue (deletePorts M.ports e)
      (fun d => MatchingCard.asMatrix (E (labels d.val))) c =
    fun x => c * (deleted M e).tensor (fun j => labels ((edgeEnum e) j).val) x := by
  funext x
  simp only [productValue,Matching.tensor,deleted,Equiv.trans_apply,
    Equiv.prodCongr_apply,Equiv.refl_apply,MatchingCard.asMatrix,Matrix.of_apply]
  congr 1
  exact (edgeEnum e).prod_comp (fun d => E (labels d.val)
    (x (deletePorts M.ports e (d,false))) (x (deletePorts M.ports e (d,true)))) |>.symm

/-- Finite sum linearity of the actual pair contraction. -/
theorem contract_sum {A : Type*} [Fintype A] (u v : P) (C : Binary (K := ℂ))
    (f : A → Tensor ℂ P) :
    contractPair u v C (fun x => ∑ a, f a x) =
      fun x => ∑ a, contractPair u v C (f a) x := by
  funext x
  simp only [contractPair,Finset.mul_sum]
  calc
    _ = ∑ i : Bool, ∑ a : A, ∑ j : Bool,
        C i j * f a (insertPair u v i j (extendRemaining u v x)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
    _ = _ := by rw [Finset.sum_comm]

/-- Contract a literal matching edge of the ancestor: only its actual label
fibre remains, with every original complex coefficient unchanged. -/
theorem contract_fiber (M : Matching P r) (weight : Label → ℂ)
    (labels : Label → Fin r → Label) (e : Fin r) (b : Label) :
    contractPair (M.ports (e,false)) (M.ports (e,true))
      (MatchingCard.asMatrix (dual b)) (Fiber.tensor M weight labels) =
    Fiber.tensor (deleted M e) (weightAfter weight labels e b) (labelsAfter labels e) := by
  change contractPair _ _ _ (fun x => ∑ a, weight a * M.tensor (labels a) x) = _
  rw [contract_sum]
  funext x
  apply Finset.sum_congr rfl
  intro a ha
  have h := contract_matched M.ports
    (fun j => MatchingCard.asMatrix (E (labels a j))) (weight a) e
    (MatchingCard.asMatrix (dual b))
  rw [MatchingCard.trace_dual] at h
  have he : productValue M.ports (fun j => MatchingCard.asMatrix (E (labels a j)))
      (weight a) = (fun y => weight a * M.tensor (labels a) y) := rfl
  rw [he] at h
  have h' := congrFun h x
  rw [product_deleted] at h'
  simpa only [productValue,Matching.tensor,MatchingCard.asMatrix,Matrix.of_apply,
    weightAfter,labelsAfter,ite_mul,one_mul,zero_mul] using h'

/-- Every genuine proper same-edge card has zero, one or four live rows. The
ancestor itself need not be a matching product. -/
theorem proper_fibre_count (M : Matching P r) (weight : Label → ℂ)
    (labels : Label → Fin r → Label) (distinguished e : Fin r)
    (hne : distinguished ≠ e) (hlabel : ∀ a, labels a distinguished = a)
    (hs : MatchingCard.PairSafe (Fiber.tensor M weight labels)) (b : Label) :
    Fintype.card {a : Label // weight a ≠ 0 ∧ labels a e = b} = 0 ∨
    Fintype.card {a : Label // weight a ≠ 0 ∧ labels a e = b} = 1 ∨
    Fintype.card {a : Label // weight a ≠ 0 ∧ labels a e = b} = 4 := by
  have huv : M.ports (e,false) ≠ M.ports (e,true) := by
    intro h
    have h' := congrArg Prod.snd (M.ports.injective h)
    exact Bool.false_ne_true h'
  have hsafe := hs _ _ huv b
  rw [contract_fiber] at hsafe
  let j := (edgeEnum e).symm ⟨distinguished,hne⟩
  have hj : ∀ a, labelsAfter labels e a j = a := by
    intro a
    simp only [labelsAfter,j,Equiv.apply_symm_apply]
    exact hlabel a
  have hc := Fiber.safe_support_card (deleted M e) (weightAfter weight labels e b)
    (labelsAfter labels e) j hj hsafe
  have he : Fintype.card {a : Label // weightAfter weight labels e b a ≠ 0} =
      Fintype.card {a : Label // weight a ≠ 0 ∧ labels a e = b} := by
    apply Fintype.card_congr
    apply Equiv.subtypeEquivRight
    intro a
    by_cases h : labels a e = b <;> simp [weightAfter,h]
  rwa [he] at hc

/-- Four surviving labels exhaust the literal four-element label space. -/
theorem all_of_card_four (p : Label → Prop) [DecidablePred p]
    (hc : Fintype.card {a : Label // p a} = 4) : ∀ a, p a := by
  intro a
  by_contra ha
  have hns : ¬ Function.Surjective (Subtype.val : {a : Label // p a} → Label) := by
    intro hs
    obtain ⟨b,hb⟩ := hs a
    exact ha (hb ▸ b.property)
  have hlt := Fintype.card_lt_of_injective_not_surjective
    (Subtype.val : {a : Label // p a} → Label) Subtype.val_injective hns
  rw [hc,card_label] at hlt
  omega

/-- Nonfactorhood forces every residual label map to be injective on the
ACTUAL live rows. Zero rows are retained and not silently made live. -/
theorem labels_injective_on_live (M : Matching P r) (hr : 2 ≤ r)
    (weight : Label → ℂ) (labels : Label → Fin r → Label)
    (distinguished : Fin r) (hlabel : ∀ a, labels a distinguished = a)
    (hn : Fiber.tensor M weight labels ≠ 0)
    (hs : MatchingCard.PairSafe (Fiber.tensor M weight labels))
    (hfactor : ¬ Fiber.HasProperTensorFactor (Fiber.tensor M weight labels))
    (e : Fin r) (a b : Label) (ha : weight a ≠ 0) (hb : weight b ≠ 0)
    (heq : labels a e = labels b e) : a = b := by
  classical
  by_cases hed : e = distinguished
  · subst e
    simpa only [hlabel] using heq
  have hde : distinguished ≠ e := Ne.symm hed
  let p : Label → Prop := fun t => weight t ≠ 0 ∧ labels t e = labels a e
  have hpa : p a := ⟨ha,rfl⟩
  have hpb : p b := ⟨hb,heq.symm⟩
  have hc := proper_fibre_count M weight labels distinguished e hde hlabel hs (labels a e)
  change Fintype.card {t : Label // p t} = 0 ∨
    Fintype.card {t : Label // p t} = 1 ∨
    Fintype.card {t : Label // p t} = 4 at hc
  rcases hc with hz | hone | hfour
  · have hp : 0 < Fintype.card {t : Label // p t} :=
      Fintype.card_pos_iff.mpr ⟨⟨a,hpa⟩⟩
    omega
  · obtain ⟨x,hx⟩ := Fintype.card_eq_one_iff.mp hone
    have hab : (⟨a,hpa⟩ : {t : Label // p t}) = ⟨b,hpb⟩ :=
      (hx ⟨a,hpa⟩).trans (hx ⟨b,hpb⟩).symm
    exact congrArg Subtype.val hab
  · have hall := all_of_card_four p hfour
    exact False.elim (hfactor (Fiber.constant_edge_factor M hr weight labels e
      (labels a e) hn (fun t ht => (hall t).2)))

/-- Once all four ACTUAL weights are proved nonzero, each label map is an
honest permutation. Full support remains an explicit separate theorem input. -/
def labelPermutation (M : Matching P r) (hr : 2 ≤ r)
    (weight : Label → ℂ) (labels : Label → Fin r → Label)
    (distinguished : Fin r) (hlabel : ∀ a, labels a distinguished = a)
    (hn : Fiber.tensor M weight labels ≠ 0)
    (hs : MatchingCard.PairSafe (Fiber.tensor M weight labels))
    (hfactor : ¬ Fiber.HasProperTensorFactor (Fiber.tensor M weight labels))
    (hlive : ∀ a, weight a ≠ 0) (e : Fin r) : Equiv.Perm Label := by
  have hi : Function.Injective (fun a => labels a e) := fun a b h =>
    labels_injective_on_live M hr weight labels distinguished hlabel hn hs hfactor
      e a b (hlive a) (hlive b) h
  exact Equiv.ofBijective (fun a => labels a e) ⟨hi,Finite.surjective_of_injective hi⟩

end
end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureExoticFiberCounts
