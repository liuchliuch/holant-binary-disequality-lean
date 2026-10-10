import Holant.Proofs.Traversal.ArityTwo.Transfer


namespace Holant.LocalDrafts.TraversalCompletion.ArityTwo.SourceExpansion
open Holant Holant.Tractable
open scoped BigOperators

theorem decomposition_of_nonzero {n : ℕ} {f : Signature AlgebraicComplex n}
    (hf : SourceTensorClosure (fun n _ => n = 1 ∨ n = 2) f) (hn : f ≠ 0) :
    ∃ D : TensorDecomposition AlgebraicComplex n,
      (∀ i, D.arity i = 1 ∨ D.arity i = 2) ∧ D.value = f := by
  rcases hf with hz | hD
  · exact (hn hz).elim
  · exact hD

variable {s : ℕ} (family : Fin s → AnySignature AlgebraicComplex)
variable (hbranch : ∀ i, SourceTensorClosure (fun n _ => n = 1 ∨ n = 2) (family i).2)
variable (hnonzero : ∀ i, (family i).2 ≠ 0)

/-- Chosen once for the fixed problem, before any network input. -/
noncomputable def decomposition (i : Fin s) : TensorDecomposition AlgebraicComplex (family i).1 :=
  Classical.choose (decomposition_of_nonzero (hbranch i) (hnonzero i))

theorem decomposition_arity (i : Fin s) (j : Fin (decomposition family hbranch hnonzero i).count) :
    (decomposition family hbranch hnonzero i).arity j = 1 ∨
      (decomposition family hbranch hnonzero i).arity j = 2 :=
  (Classical.choose_spec (decomposition_of_nonzero (hbranch i) (hnonzero i))).1 j

theorem decomposition_exact (i : Fin s) (x : Fin (family i).1 → Bool) :
    (family i).2 x =
      ((decomposition family hbranch hnonzero i).scale : AlgebraicComplex) *
        ∏ j, (decomposition family hbranch hnonzero i).factor j
          (fun p => x ((decomposition family hbranch hnonzero i).ports ⟨j,p⟩)) := by
  exact congrFun (Classical.choose_spec
    (decomposition_of_nonzero (hbranch i) (hnonzero i))).2.symm x

theorem port_count (i : Fin s) :
    ∑ j, (decomposition family hbranch hnonzero i).arity j = (family i).1 := by
  simpa only [Fintype.card_sigma,Fintype.card_fin] using
    Fintype.card_congr (decomposition family hbranch hnonzero i).ports

theorem factor_count_le_arity (i : Fin s) :
    (decomposition family hbranch hnonzero i).count ≤ (family i).1 := by
  have hb : ∑ _j : Fin (decomposition family hbranch hnonzero i).count, 1 ≤
      ∑ j, (decomposition family hbranch hnonzero i).arity j := by
    apply Finset.sum_le_sum
    intro j _
    rcases decomposition_arity family hbranch hnonzero i j with hj | hj <;> omega
  simpa only [Finset.sum_const,Fintype.card_fin,Finset.card_univ,smul_eq_mul,mul_one,
    port_count family hbranch hnonzero i] using hb

/-- Every occurrence expands to at most this fixed number of factor vertices,
including its normalization scalar as a separate nullary component. -/
noncomputable def expansionBound : ℕ :=
  ∑ i, ((decomposition family hbranch hnonzero i).count+1)

theorem expansion_count_le (i : Fin s) :
    (decomposition family hbranch hnonzero i).count+1 ≤ expansionBound family hbranch hnonzero :=
  by
    unfold expansionBound
    exact Finset.single_le_sum (f := fun j => (decomposition family hbranch hnonzero j).count + 1) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

/-- Addresses of the finitely many expanded tensor entries and scale factors.
No entry is computed from the varying input instance. -/
abbrev Literal :=
  (Σ i : Fin s, Σ j : Fin (decomposition family hbranch hnonzero i).count,
    Fin ((decomposition family hbranch hnonzero i).arity j) → Bool) ⊕ Fin s

noncomputable def coefficient : Literal family hbranch hnonzero → AlgebraicComplex
  | .inl ⟨i,j,x⟩ => (decomposition family hbranch hnonzero i).factor j x
  | .inr i => ((decomposition family hbranch hnonzero i).scale : AlgebraicComplex)

end Holant.LocalDrafts.TraversalCompletion.ArityTwo.SourceExpansion
