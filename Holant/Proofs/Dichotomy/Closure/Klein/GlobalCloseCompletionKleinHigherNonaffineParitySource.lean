import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinHigherNonaffineParityActual

/-! Actual family-wide parity producer. A mixed-parity saved row selects a
mixed-parity retained prime through its complete factor tree. The original
no-unary/no-odd guards put that prime in the even descent domain, giving an
actual nonmatching q4. This theorem applies to all saved rows, not only the
chosen stable minimum. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffineParitySource
open Holant Holant.Tractable Holant.Algebraic
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.Projective.BoundedTorsion hiding binarySignature
open GlobalCloseCompletionKleinHigherNonaffineParity
open GlobalCloseCompletionProductAncestorParity
namespace D
export GlobalCloseCompletionKleinHigherNonaffineParityActual
  (phi complexTensor arity arity_eq from_actual nonparity_not_matching)
end D
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false

private theorem parity_factorTree {L : Type*} [Field L]
    {f : AnySignature L} (tree : FactorTree f)
    (leaves : ∀g∈tree.leaves,PureParity g.2) : PureParity f.2 := by
  induction tree with
  | leaf f prime => exact leaves f (by simp [FactorTree.leaves])
  | @split f a b split left right ihl ihr =>
    exact pureParity_split split
      (ihl (fun g hg=>leaves g (Multiset.mem_add.mpr (Or.inl hg))))
      (ihr (fun g hg=>leaves g (Multiset.mem_add.mpr (Or.inr hg))))

private theorem nonparity_leaf {L : Type*} [Field L]
    {f : AnySignature L} (tree : FactorTree f) (bad : ¬PureParity f.2) :
    ∃g∈tree.leaves,¬PureParity g.2 := by
  classical
  by_contra! none
  exact bad (parity_factorTree tree none)

variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (cardinal : Nat.card (completeGroup P.family torsion)=4)
variable (noncyclic : ¬IsCyclic (completeGroup P.family torsion))
variable (standard : ClosureKleinCurrent.kind G P torsion cardinal noncyclic=.standard)
variable (noUnary : ¬RetainedUnary P.family)
variable (noOdd : ∀g∈P.family,Prime g→3≤g.1→Even g.1)

theorem mapped_parity_iff {n : ℕ} (f : Signature (OI.K G) n) :
    HasParity (D.complexTensor G f) ↔ PureParity f :=
  (hasParity_iff _).trans (pureParity_map_iff (D.phi G) f)

include cardinal noncyclic standard noUnary in
theorem nonparity_prime_nonbinary (g : AnySignature (OI.K G)) (retained : g∈P.family)
    (prime : Prime g) (bad : ¬PureParity g.2) : 3≤g.1 := by
  have positive : 0<g.1 := by obtain ⟨j,hj⟩ := retained;rw [←hj];exact P.positive j
  by_contra small
  have cases : g.1=1 ∨ g.1=2 := by omega
  rcases g with ⟨m,f⟩
  rcases cases with rfl|rfl
  · exact noUnary ⟨f,retained,prime.1⟩
  · have badMap : ¬HasParity (D.complexTensor G f) := fun h=>bad ((mapped_parity_iff G f).mp h)
    apply D.nonparity_not_matching G P torsion cardinal noncyclic standard f badMap
    apply FactorTree.matchingOrZero (.leaf ⟨2,f⟩ prime) P.family
    · intro h hh
      have eq : h=(⟨2,f⟩ : AnySignature (OI.K G)) := by
        simpa only [FactorTree.leaves,Multiset.mem_singleton] using hh
      exact eq.symm ▸ retained
    · intro h hh
      have eq : h=(⟨2,f⟩ : AnySignature (OI.K G)) := by
        simpa only [FactorTree.leaves,Multiset.mem_singleton] using hh
      exact congrArg Sigma.fst eq

include cardinal noncyclic standard noUnary noOdd in
theorem retained_nonparity_source (i : Fin P.count) (bad : ¬PureParity (P.table i)) :
    Nonempty (GlobalCloseCompletionKleinQuaternaryRestart.D.Output G P) := by
  obtain ⟨g,hg,badg⟩ := nonparity_leaf (P.trees i) bad
  have retained := P.leavesRetained i g hg
  have prime := (P.trees i).leaves_prime g hg
  have nonbinary := nonparity_prime_nonbinary G P torsion cardinal noncyclic standard noUnary g retained prime badg
  have even := noOdd g retained prime nonbinary
  rcases g with ⟨m,f⟩
  obtain ⟨k,hk⟩ := even
  change m=k+k at hk
  change 3≤m at nonbinary
  have lower : 2≤k := by omega
  have size : m=D.arity (k-2) := by rw [D.arity_eq];omega
  clear hk
  subst m
  refine ⟨D.from_actual G P torsion cardinal noncyclic standard (k-2) f
    (Gadget.realizes_of_mem _ .disequality f retained) ?_⟩
  exact fun h=>badg ((mapped_parity_iff G f).mp h)

include cardinal noncyclic standard noUnary noOdd in
theorem all_parity_or_quaternary :
    (∀i : Fin P.count,PureParity (P.table i)) ∨
      Nonempty (GlobalCloseCompletionKleinQuaternaryRestart.D.Output G P) := by
  classical
  by_cases all : ∀i : Fin P.count,PureParity (P.table i)
  · exact Or.inl all
  · push Not at all
    obtain ⟨i,bad⟩ := all
    exact Or.inr (retained_nonparity_source G P torsion cardinal noncyclic standard noUnary noOdd i bad)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffineParitySource
end
