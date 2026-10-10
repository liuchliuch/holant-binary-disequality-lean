import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinHigherNonaffineCharacterMatching

/-! Current guarded parity and the exact nonbinary domains for retained
noncharacter and nonaffine primes. Saved complete trees also force every
retained row, including a newly installed programme output, to have even arity. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffinePredicateBounds
open Holant Holant.Tractable Holant.Algebraic Holant.Marked
open Holant.Certificates Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.Projective.BoundedTorsion hiding binarySignature
namespace C
export GlobalCloseCompletionRetainedCharacterLeaf (Predicate)
end C
namespace A
export GlobalCloseCompletionKleinAffineLeaf (IsAffine)
end A
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false

 theorem tree_even {K : Type*} [Field K] {f : AnySignature K} (tree : FactorTree f)
    (leaves : ∀g∈tree.leaves,Even g.1) : Even f.1 := by
  induction tree with
  | leaf f prime => exact leaves f (by simp [FactorTree.leaves])
  | @split f a b split left right ihl ihr =>
    rw [←split.arity]
    exact (ihl (fun g hg=>leaves g (Multiset.mem_add.mpr (Or.inl hg)))).add
      (ihr (fun g hg=>leaves g (Multiset.mem_add.mpr (Or.inr hg))))

variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G)
variable (noUnary : ¬RetainedUnary P.family)
variable (noOdd : ∀g∈P.family,Prime g→3≤g.1→Even g.1)

include noUnary noOdd in
theorem retained_prime_even (g : AnySignature (OI.K G)) (retained : g∈P.family) (prime : Prime g) : Even g.1 := by
  by_cases large : 3≤g.1
  · exact noOdd g retained prime large
  have positive : 0<g.1 := by obtain ⟨i,hi⟩ := retained;rw [←hi];exact P.positive i
  have cases : g.1=1 ∨ g.1=2 := by omega
  rcases g with ⟨m,f⟩
  rcases cases with rfl|rfl
  · exact (noUnary ⟨f,retained,prime.1⟩).elim
  · change Even (2 : ℕ);decide

include noUnary noOdd in
theorem retained_even (g : AnySignature (OI.K G)) (retained : g∈P.family) : Even g.1 := by
  obtain ⟨i,rfl⟩ := retained
  apply tree_even (P.trees i)
  intro q hq
  exact retained_prime_even G P noUnary noOdd q (P.leavesRetained i q hq) ((P.trees i).leaves_prime q hq)

variable (torsion : ResidualTorsion P.family)
variable (cardinal : Nat.card (completeGroup P.family torsion)=4)
variable (noncyclic : ¬IsCyclic (completeGroup P.family torsion))
variable (standard : ClosureKleinCurrent.kind G P torsion cardinal noncyclic=.standard)

include cardinal noncyclic standard noUnary in
theorem noncharacter_prime_nonbinary (g : AnySignature (OI.K G)) (retained : g∈P.family)
    (prime : Prime g) (bad : ¬C.Predicate G g) : 3≤g.1 := by
  have positive : 0<g.1 := by obtain ⟨i,hi⟩ := retained;rw [←hi];exact P.positive i
  by_contra small
  have cases : g.1=1 ∨ g.1=2 := by omega
  rcases g with ⟨m,f⟩
  rcases cases with rfl|rfl
  · exact noUnary ⟨f,retained,prime.1⟩
  · apply bad
    apply GlobalCloseCompletionKleinHigherNonaffineCharacterMatching.current_matching_character
      G P torsion cardinal noncyclic standard f
    apply FactorTree.matchingOrZero (.leaf ⟨2,f⟩ prime) P.family
    · intro h hh
      have eq : h=(⟨2,f⟩ : AnySignature (OI.K G)) := by simpa only [FactorTree.leaves,Multiset.mem_singleton] using hh
      exact eq.symm ▸ retained
    · intro h hh
      have eq : h=(⟨2,f⟩ : AnySignature (OI.K G)) := by simpa only [FactorTree.leaves,Multiset.mem_singleton] using hh
      exact congrArg Sigma.fst eq

include cardinal noncyclic standard noUnary noOdd in
theorem noncharacter_prime_domain (g : AnySignature (OI.K G)) (retained : g∈P.family)
    (prime : Prime g) (bad : ¬C.Predicate G g) : 4≤g.1 ∧ Even g.1 := by
  have lower := noncharacter_prime_nonbinary G P noUnary torsion cardinal noncyclic standard g retained prime bad
  have even := noOdd g retained prime lower
  refine ⟨?_,even⟩
  obtain ⟨k,hk⟩ := even
  omega

include cardinal noncyclic standard noUnary noOdd in
theorem nonaffine_prime_domain (g : AnySignature (OI.K G)) (retained : g∈P.family)
    (prime : Prime g) (bad : ¬A.IsAffine G g) : 4≤g.1 ∧ Even g.1 := by
  have lower := GlobalCloseCompletionKleinStandardMatchingAffine.nonaffine_prime_nonbinary
    G P torsion cardinal noncyclic standard noUnary g retained prime bad
  have even := noOdd g retained prime lower
  refine ⟨?_,even⟩
  obtain ⟨k,hk⟩ := even
  omega


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffinePredicateBounds
end
