import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinAffineLeaf
import Holant.Tractable.SymmetricBinaryPullback.LocalAffine

/-! Every actual standard-Pauli matching product is Affine in the same native
coordinates. Thus a nonaffine retained prime cannot be a binary Pauli factor.
No claim about arbitrary higher nonmatching signatures is made. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinStandardMatchingAffine
open Holant Holant.Tractable Holant.Algebraic Holant.Marked
open Holant.Certificates Holant.Certificates.MatchingContractionClosure
open Holant.Tractable.AffinePhase Holant.Tractable.TwoTranslate
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.Projective.BoundedTorsion hiding binarySignature
open scoped BigOperators
namespace K
export EqualityQuaternary.Klein (E)
end K
namespace A
export GlobalCloseCompletionKleinAffineLeaf (IsAffine Minimum)
end A
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false

def flipSecond (x : Fin 2→Bool) : Fin 2→Bool := ![x 0,!(x 1)]
theorem flipSecond_affine : IsAffineMap flipSecond := by unfold IsAffineMap; decide

theorem E_affine (k : Fin 4) : Affine (kernelSignature (K.E .standard k)) := by
  have plus := SymmetricBinaryPullback.affine_diagonal_of_fourth_power_eq
    (1 : AlgebraicComplex) 1 one_ne_zero rfl
  have minus := SymmetricBinaryPullback.affine_diagonal_of_fourth_power_eq
    (1 : AlgebraicComplex) (-1) one_ne_zero (by norm_num)
  fin_cases k
  · convert plus using 1
    funext x
    cases h0 : x 0 <;> cases h1 : x 1 <;>
      norm_num [kernelSignature,K.E,EqualityQuaternary.Klein.basisQ,EqualityQuaternary.Klein.matrix,
        EqualityQuaternary.Klein.embed_apply,QuadraticAlgebra.re_one,QuadraticAlgebra.im_one,
        SymmetricBinaryPullback.diagonal,h0,h1]
  · convert plus.precompose flipSecond flipSecond_affine using 1
    funext x
    cases h0 : x 0 <;> cases h1 : x 1 <;>
      norm_num [kernelSignature,K.E,EqualityQuaternary.Klein.basisQ,EqualityQuaternary.Klein.matrix,
        EqualityQuaternary.Klein.embed_apply,QuadraticAlgebra.re_one,QuadraticAlgebra.im_one,
        SymmetricBinaryPullback.diagonal,flipSecond,h0,h1]
  · convert minus using 1
    funext x
    cases h0 : x 0 <;> cases h1 : x 1 <;>
      norm_num [kernelSignature,K.E,EqualityQuaternary.Klein.basisQ,EqualityQuaternary.Klein.matrix,
        EqualityQuaternary.Klein.embed_apply,QuadraticAlgebra.re_one,QuadraticAlgebra.im_one,
        SymmetricBinaryPullback.diagonal,h0,h1]
  · convert minus.precompose flipSecond flipSecond_affine using 1
    funext x
    cases h0 : x 0 <;> cases h1 : x 1 <;>
      norm_num [kernelSignature,K.E,EqualityQuaternary.Klein.basisQ,EqualityQuaternary.Klein.matrix,
        EqualityQuaternary.Klein.embed_apply,QuadraticAlgebra.re_one,QuadraticAlgebra.im_one,
        SymmetricBinaryPullback.diagonal,flipSecond,h0,h1]

theorem canonical_affine {n : ℕ} (f : Signature AlgebraicComplex n)
    (matching : ClosureKleinCurrent.CanonicalMatching .standard f) : Affine f := by
  classical
  rcases matching with rfl|⟨M,labels,_hc,matrices,rfl⟩
  · exact affine_zero n
  have single (e : Fin M.edges) : Affine (fun x=>
      K.E .standard (labels e) (x (M.ports (e,false))) (x (M.ports (e,true)))) := by
    let indices : Fin 2→Fin n := ![M.ports (e,false),M.ports (e,true)]
    exact (E_affine (labels e)).precompose (fun x j=>x (indices j)) (coordinates_isAffineMap indices)
  have product (S : Finset (Fin M.edges)) : Affine (fun x=>∏e∈S,
      K.E .standard (labels e) (x (M.ports (e,false))) (x (M.ports (e,true)))) := by
    induction S using Finset.induction_on with
    | empty => simpa using affine_constant n 1
    | @insert e S notmem ih =>
      simpa only [Finset.prod_insert notmem] using (single e).mul ih
  change Affine (fun x=>M.scalar*∏e,M.matrix e (x (M.ports (e,false))) (x (M.ports (e,true))))
  simpa only [matrices] using (product Finset.univ).scale M.scalar

variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (cardinal : Nat.card (completeGroup P.family torsion)=4)
variable (noncyclic : ¬IsCyclic (completeGroup P.family torsion))
variable (standard : ClosureKleinCurrent.kind G P torsion cardinal noncyclic=.standard)

include cardinal noncyclic standard in
theorem current_matching_affine {n : ℕ} (f : Signature (OI.K G) n)
    (matching : MatchingOrZero (actualTransfers P.family) f) :
    Affine (RingHomRealization.mapSignature (ClosureSourceRows.embedding G) f) := by
  have h := ClosureKleinCurrent.matching_mapped G P torsion cardinal noncyclic f matching
  rw [standard] at h
  exact canonical_affine _ h

include cardinal noncyclic standard in
theorem nonaffine_prime_nonbinary (noUnary : ¬RetainedUnary P.family)
    (g : AnySignature (OI.K G)) (retained : g∈P.family) (prime : Prime g)
    (bad : ¬A.IsAffine G g) : 3≤g.1 := by
  have positive : 0<g.1 := by obtain ⟨i,hi⟩ := retained;rw [←hi];exact P.positive i
  by_contra small
  have cases : g.1=1 ∨ g.1=2 := by omega
  rcases g with ⟨m,f⟩
  rcases cases with rfl|rfl
  · exact noUnary ⟨f,retained,prime.1⟩
  · apply bad
    apply current_matching_affine G P torsion cardinal noncyclic standard f
    apply FactorTree.matchingOrZero (.leaf ⟨2,f⟩ prime) P.family
    · intro h hh
      have eq : h=(⟨2,f⟩ : AnySignature (OI.K G)) := by simpa only [FactorTree.leaves,Multiset.mem_singleton] using hh
      exact eq.symm ▸ retained
    · intro h hh
      have eq : h=(⟨2,f⟩ : AnySignature (OI.K G)) := by simpa only [FactorTree.leaves,Multiset.mem_singleton] using hh
      exact congrArg Sigma.fst eq

include cardinal noncyclic standard in
theorem minimum_nonbinary (noUnary : ¬RetainedUnary P.family) (M : A.Minimum G P) : 3≤M.signature.1 :=
  nonaffine_prime_nonbinary G P torsion cardinal noncyclic standard noUnary M.signature M.retained M.prime M.bad


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinStandardMatchingAffine
end
