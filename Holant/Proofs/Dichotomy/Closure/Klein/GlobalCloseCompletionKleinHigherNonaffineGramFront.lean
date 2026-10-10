import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinGramAllPairs

/-! Front-pair version of the actual real Gram producer, in the recursive
arity convention used by RM coordinate programs. The port cast is proved
entrywise and consumes no signature resource. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffineGramFront
open Holant Holant.Tractable Holant.Algebraic
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Dihedral.CompatibleCoefficientLine (pair)
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false

def order (n : ℕ) : Fin (n+2)≃Fin (2+n) := finCongr (Nat.add_comm n 2)

theorem cast_pair (n : ℕ) (u : Fin 2→Bool) (z : Fin n→Bool) :
    (fun i=>Fin.addCases (m:=2) (n:=n) u z (order n i))=pair (u 0) (u 1) z := by
  funext i
  refine Fin.cases ?_ (fun j=>Fin.cases ?_ (fun k=>?_) j) i
  · have h : order n 0=Fin.castAdd n (0:Fin 2) := by apply Fin.ext;rfl
    rw [h,Fin.addCases_left]
    rfl
  · have h : order n 1=Fin.castAdd n (1:Fin 2) := by apply Fin.ext;simp [order]
    change Fin.addCases u z (order n 1)=u 1
    rw [h,Fin.addCases_left]
  · have h : order n k.succ.succ=Fin.natAdd 2 k := by apply Fin.ext;simp [order];omega
    rw [h,Fin.addCases_right]
    rfl

theorem realizes_reindex_any {K : Type*} [Field K] {m n : ℕ}
    (F : SignatureFamily K) (e : Fin m≃Fin n) (f : Signature K m)
    (actual : Gadget.Realizes F .disequality f) : Gadget.Realizes F .disequality (Tensor.reindex e f) := by
  have mn : m=n := by simpa using Fintype.card_congr e
  subst n
  exact Holant.Dihedral.CompatibleClosure.realizes_reindex F .disequality f actual e.symm

theorem prime_reindex_any {K : Type*} [Field K] {m n : ℕ}
    (e : Fin m≃Fin n) (f : Signature K m) (prime : Prime (⟨m,f⟩ : AnySignature K)) :
    Prime (⟨n,Tensor.reindex e f⟩ : AnySignature K) := by
  have mn : m=n := by simpa using Fintype.card_congr e
  subst n
  exact GlobalCloseCompletionKleinGramAllPairs.prime_reindex f prime e

variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (cardinal : Nat.card (completeGroup P.family torsion)=4)
variable (noncyclic : ¬IsCyclic (completeGroup P.family torsion))
variable (standard : ClosureKleinCurrent.kind G P torsion cardinal noncyclic=.standard)

include cardinal noncyclic standard in
theorem orthogonal_or_quaternary {n : ℕ} (positive : 0<n) (f : Signature (OI.K G) (n+2))
    (prime : Prime (⟨n+2,f⟩ : AnySignature (OI.K G))) (actual : Gadget.Realizes P.family .disequality f)
    (r : Signature ℝ (n+2)) (c : ℂ) (hc : c≠0)
    (normal : RingHomRealization.mapSignature (ClosurePhysicalBridge.complexEmbedding G) f=fun x=>c*(r x:ℂ)) :
    (∃d : ℂ,∀u v : Fin 2→Bool,
      (∑z : Fin n→Bool,
        ClosurePhysicalBridge.complexEmbedding G (f (pair (u 0) (u 1) z))*
        ClosurePhysicalBridge.complexEmbedding G (f (pair (v 0) (v 1) z)))=if u=v then d else 0) ∨
    ∃q : Signature (OI.K G) 4,q≠0 ∧ Gadget.Realizes P.family .disequality q ∧
      ¬MatchingOrZero (actualTransfers P.family) q := by
  have norm : RingHomRealization.mapSignature (ClosurePhysicalBridge.complexEmbedding G) (Tensor.reindex (order n) f)=
      fun x=>c*((Tensor.reindex (order n) r x:ℝ):ℂ) := by
    funext x
    exact congrFun normal (fun i=>x (order n i))
  rcases GlobalCloseCompletionKleinGramCurrent.orthogonal_or_quaternary
    G P torsion cardinal noncyclic standard (Tensor.reindex (order n) f) positive
    (prime_reindex_any (order n) f prime) (realizes_reindex_any P.family (order n) f actual)
    (Tensor.reindex (order n) r) c hc norm with ortho|q
  · left
    obtain ⟨d,_positive,rows⟩ := ortho
    have rr (u v : Fin 2→Bool) :
        (∑z : Fin n→Bool,r (pair (u 0) (u 1) z)*r (pair (v 0) (v 1) z))=if u=v then d else 0 := by
      simpa only [Tensor.reindex,cast_pair] using rows u v
    refine ⟨c^2*(d:ℂ),?_⟩
    intro u v
    have value (x : Fin (n+2)→Bool) : ClosurePhysicalBridge.complexEmbedding G (f x)=c*(r x:ℂ) :=
      congrFun normal x
    simp_rw [value]
    have term (z : Fin n→Bool) :
        (c*(r (pair (u 0) (u 1) z):ℂ))*(c*(r (pair (v 0) (v 1) z):ℂ))=
          c^2*((r (pair (u 0) (u 1) z)*r (pair (v 0) (v 1) z):ℝ):ℂ) := by
      rw [Complex.ofReal_mul]
      ring
    simp_rw [term]
    rw [←Finset.mul_sum,←Complex.ofReal_sum,rr]
    split_ifs <;> simp
  · exact Or.inr q

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffineGramFront
end
