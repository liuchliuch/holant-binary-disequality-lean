import Holant.Platonic.TetrahedralLocalization.Collection

/-! Finite physical pair descent, flattened into a single collection on the
original ports. The endpoint is nonaffine and either has at most eight ports
or exposes a genuine tensor factor. No continuing-state oracle is assumed. -/
namespace Holant.Platonic.TetrahedralLocalization
open Holant Holant.Platonic.StabilizerShortening Holant.Platonic.StabilizerLine
open Holant.Certificates.MatchingContractionClosure Holant.Certificates.TetrahedralAffine
open Holant.Pauli.ExoticKlein.Fiber
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

/-- Finite actual representative choices and their disjoint original ports. -/
structure PairCollection (o n : ℕ) where
  Edge : Type
  [finite : Fintype Edge]
  [decidable : DecidableEq Edge]
  ports : CollectionPorts (Fin o) (Fin n) Edge
  representative : Edge → Representative

attribute [instance] PairCollection.finite PairCollection.decidable

variable {o m n : ℕ}

def PairCollection.value (C : PairCollection o n) (f : Signature ℂ o) : Signature ℂ n :=
  contractCollection C.ports (fun e => complexKernel (C.representative e)) f

def PairCollection.empty (n : ℕ) : PairCollection n n where
  Edge := Empty
  ports := emptyPorts n
  representative e := nomatch e

@[simp] theorem PairCollection.empty_value (f : Signature ℂ n) :
    (PairCollection.empty n).value f=f := emptyCollection f

def PairCollection.add (C : PairCollection o m) (p : (Bool ⊕ Fin n) ≃ Fin m)
    (r : Representative) : PairCollection o n where
  Edge := Option C.Edge
  ports := addPairPorts C.ports p
  representative := Option.elim' r C.representative

@[simp] theorem PairCollection.add_value (C : PairCollection o m)
    (p : (Bool ⊕ Fin n) ≃ Fin m) (r : Representative) (f : Signature ℂ o) :
    (C.add p r).value f=pairCard p (complexKernel r) (C.value f) := by
  unfold PairCollection.value PairCollection.add
  convert contractCollection_addPair C.ports p
    (fun e => complexKernel (C.representative e)) (complexKernel r) f using 1
  congr 1
  ext e
  cases e <;> rfl

@[simp] theorem PairCollection.add_count (C : PairCollection o m)
    (p : (Bool ⊕ Fin n) ≃ Fin m) (r : Representative) :
    Fintype.card (C.add p r).Edge=Fintype.card C.Edge+1 := Fintype.card_option

theorem PairCollection.arity (C : PairCollection o n) : n+2*Fintype.card C.Edge=o :=
  collection_arity C.ports

theorem PairCollection.exact_count (C : PairCollection o n) :
    Fintype.card C.Edge=(o-n)/2 := by
  have h := C.arity
  omega

theorem PairCollection.linear_count (C : PairCollection o n) :
    Fintype.card C.Edge≤o/2 := by
  have h := C.arity
  omega

/-- Arity well-founded induction proves termination of the actual pair descent.
Every recursive call retains the same original f and appends one real kernel. -/
theorem continue_descent (f : Signature ℂ o) : ∀m : ℕ,∀C : PairCollection o m,
    ¬ComplexAffine (C.value f) →
    ∃n : ℕ,∃D : PairCollection o n,
      ¬ComplexAffine (D.value f) ∧ (n≤8 ∨ HasProperTensorFactor (D.value f)) := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro C hC
    by_cases hm : m≤8
    · exact ⟨m,C,hC,Or.inl hm⟩
    rcases factor_or_nonaffine_pair (C.value f) (by omega) hC with hf|hc
    · exact ⟨m,C,hC,Or.inr hf⟩
    · obtain ⟨n,p,r,_,ha⟩ := hc
      have hp := pair_arity p
      apply ih n (by omega) (C.add p r)
      simpa only [PairCollection.add_value] using ha

/-- The complete finite descent conclusion, with original-port provenance and
an exact, hence linear, count of chosen tetrahedral binary representatives. -/
theorem source_finite_descent (f : Signature ℂ o) (hf : ¬ComplexAffine f) :
    ∃n : ℕ,∃C : PairCollection o n,
      C.value f≠0 ∧ ¬ComplexAffine (C.value f) ∧
      (n≤8 ∨ HasProperTensorFactor (C.value f)) ∧
      n+2*Fintype.card C.Edge=o ∧ Fintype.card C.Edge=(o-n)/2 ∧
      Fintype.card C.Edge≤o/2 := by
  obtain ⟨n,C,hC,hexit⟩ := continue_descent f o (PairCollection.empty o) (by simpa using hf)
  exact ⟨n,C,(fun hz => hC (hz ▸ affine_zero_complex)),hC,hexit,
    C.arity,C.exact_count,C.linear_count⟩

end
end Holant.Platonic.TetrahedralLocalization
