import Holant.Certificates.MatchingContractionClosure.Interface

/-! Every surviving ordered-pair card commutes with the disjoint original-port
closure collection.  No matching assumption is used in this finite-sum identity. -/
noncomputable section
namespace Holant.Platonic.RainbowLocalization.Physical
open Holant Holant.Certificates.MatchingContractionClosure
open scoped BigOperators
variable {P Q E : Type*} [DecidableEq P] [DecidableEq Q] [DecidableEq E]

def boundaryPairMap (p : CollectionPorts P Q E) (u v : Q) :
    (Remaining u v ⊕ (E × Bool)) → Remaining (p (.inl u)) (p (.inl v))
  | .inl q => ⟨p (.inl q.val),by
      constructor <;> intro h
      · exact q.property.1 (Sum.inl.inj (p.injective h))
      · exact q.property.2 (Sum.inl.inj (p.injective h))⟩
  | .inr eb => ⟨p (.inr eb),by constructor <;> intro h <;> cases p.injective h⟩

def boundaryPairPorts (p : CollectionPorts P Q E) (u v : Q) :
    CollectionPorts (Remaining (p (.inl u)) (p (.inl v))) (Remaining u v) E :=
  Equiv.ofBijective (boundaryPairMap p u v) (by
    constructor
    · intro a b h
      have hh := congrArg (fun q : Remaining (p (.inl u)) (p (.inl v)) => p.symm q.val) h
      cases a with
      | inl a =>
        cases b with
        | inl b =>
          simp only [boundaryPairMap,Equiv.symm_apply_apply] at hh
          exact congrArg Sum.inl (Subtype.ext (Sum.inl.inj hh))
        | inr b =>
          simp only [boundaryPairMap,Equiv.symm_apply_apply] at hh
          cases hh
      | inr a =>
        cases b with
        | inl b =>
          simp only [boundaryPairMap,Equiv.symm_apply_apply] at hh
          cases hh
        | inr b =>
          simp only [boundaryPairMap,Equiv.symm_apply_apply] at hh
          exact congrArg Sum.inr (Sum.inr.inj hh)
    · intro q
      obtain ⟨a,ha⟩ := p.surjective q.val
      cases a with
      | inl a =>
        have hu : a ≠ u := fun h => q.property.1 (ha.symm.trans (congrArg (fun z => p (.inl z)) h))
        have hv : a ≠ v := fun h => q.property.2 (ha.symm.trans (congrArg (fun z => p (.inl z)) h))
        exact ⟨.inl ⟨a,hu,hv⟩,Subtype.ext ha⟩
      | inr a => exact ⟨.inr a,Subtype.ext ha⟩)

@[simp] theorem boundaryPairPorts_boundary (p : CollectionPorts P Q E) (u v : Q)
    (q : Remaining u v) : (boundaryPairPorts p u v (.inl q)).val = p (.inl q.val) := rfl

@[simp] theorem boundaryPairPorts_edge (p : CollectionPorts P Q E) (u v : Q)
    (e : E) (b : Bool) : (boundaryPairPorts p u v (.inr (e,b))).val = p (.inr (e,b)) := rfl

theorem boundary_pair_distinct (p : CollectionPorts P Q E) (u v : Q) (huv : u ≠ v) :
    p (.inl u) ≠ p (.inl v) := fun h => huv (Sum.inl.inj (p.injective h))

theorem collectionAssignment_insert_boundary (p : CollectionPorts P Q E) (u v : Q) (huv : u ≠ v)
    (x : Remaining u v → Bool) (y : E → Bool × Bool) (a b : Bool) :
    collectionAssignment p (insertPair u v a b (extendRemaining u v x)) y =
      insertPair (p (.inl u)) (p (.inl v)) a b
        (extendRemaining _ _ (collectionAssignment (boundaryPairPorts p u v) x y)) := by
  funext i
  obtain ⟨z,rfl⟩ := p.surjective i
  cases z with
  | inl q =>
    rw [collectionAssignment_boundary]
    by_cases hqu : q = u
    · subst q
      rw [insertPair_first huv,insertPair_first (boundary_pair_distinct p u v huv)]
    by_cases hqv : q = v
    · subst q
      rw [insertPair_second,insertPair_second]
    rw [insertPair_other hqu hqv,insertPair_other]
    · change extendRemaining u v x (⟨q,hqu,hqv⟩ : Remaining u v).val =
        extendRemaining _ _ (collectionAssignment (boundaryPairPorts p u v) x y)
          (boundaryPairPorts p u v (.inl ⟨q,hqu,hqv⟩)).val
      rw [extendRemaining_apply,extendRemaining_apply,collectionAssignment_boundary]
    · exact fun h => hqu (Sum.inl.inj (p.injective h))
    · exact fun h => hqv (Sum.inl.inj (p.injective h))
  | inr eb =>
    rcases eb with ⟨e,t⟩
    rw [collectionAssignment_edge,insertPair_other]
    · change (if t then (y e).2 else (y e).1) =
        extendRemaining _ _ (collectionAssignment (boundaryPairPorts p u v) x y)
          (boundaryPairPorts p u v (.inr (e,t))).val
      rw [extendRemaining_apply,collectionAssignment_edge]
    · intro h; cases p.injective h
    · intro h; cases p.injective h

variable {K : Type*} [Field K] [Fintype E]

/-- Exact Fubini commutation for every surviving ordered pair and every
literal kernel, including zero or singular card values. -/
theorem contractPair_contractCollection (p : CollectionPorts P Q E)
    (C : E → Binary (K := K)) (f : Tensor K P) (u v : Q) (huv : u ≠ v)
    (B : Binary (K := K)) :
    contractPair u v B (contractCollection p C f) =
      contractCollection (boundaryPairPorts p u v) C
        (contractPair (p (.inl u)) (p (.inl v)) B f) := by
  funext x
  simp only [contractPair,contractCollection,Finset.mul_sum]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset Bool))
    (t := (Finset.univ : Finset (E → Bool × Bool)))]
  apply Finset.sum_congr rfl
  intro y hy
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  rw [collectionAssignment_insert_boundary p u v huv]
  ring

/-- The inherited all-card condition after any disjoint closure uses the
existing actual matching-contraction theorem on the corresponding original card. -/
theorem all_cards_after_collection (G : Set (Binary (K := K))) (hG : ProjectiveMatrixGroup G)
    (hX : (X : Binary (K := K)) ∈ G) (hrev : ReversalStable G)
    (D : Set (Binary (K := K))) (p : CollectionPorts P Q E)
    (C : E → Binary (K := K)) (f : Tensor K P) (hC : ∀ e, SafeBinary G (C e))
    (hdeck : ∀ u v, u ≠ v → ∀ B ∈ D, MatchingOrZero G (contractPair u v B f)) :
    ∀ u v, u ≠ v → ∀ B ∈ D,
      MatchingOrZero G (contractPair u v B (contractCollection p C f)) := by
  intro u v huv B hB
  rw [contractPair_contractCollection p C f u v huv B]
  exact contractCollection_closed hG hX hrev _ C _ hC
    (hdeck _ _ (boundary_pair_distinct p u v huv) B hB)

end Holant.Platonic.RainbowLocalization.Physical
