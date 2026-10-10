import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinGramCurrent

/-! Simultaneous second-order orthogonality in every original port order,
or one actual nonmatching quaternary. The real normalization scalar is common
to all orders, and the order changes are actual boundary permutations. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinGramAllPairs
open Holant Holant.Tractable Holant.Algebraic Holant.Marked
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.Projective.BoundedTorsion hiding binarySignature
namespace N
export GlobalCloseCompletionKleinGramNorm (OrthogonalPair)
end N
namespace RH
export RingHomRealization (mapSignature)
end RH
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type*} [Field K]

theorem prime_reindex {n : ℕ} (f : Signature K n) (prime : Prime (⟨n,f⟩ : AnySignature K))
    (p : Equiv.Perm (Fin n)) : Prime (⟨n,Tensor.reindex p f⟩ : AnySignature K) := by
  constructor
  · intro zero
    apply prime.1
    have h := congrArg (Tensor.reindex p.symm) zero
    rw [Tensor.reindex_symm] at h
    exact h
  · rintro ⟨a,b,⟨split⟩⟩
    apply prime.2
    refine ⟨a,b,⟨⟨split.left_pos,split.right_pos,split.ports.trans p.symm,split.scale,?_⟩⟩⟩
    funext x
    have h := congrFun split.equation (fun i=>x (p.symm i))
    simpa only [Tensor.reindex,Equiv.symm_apply_apply,Equiv.trans_apply] using h

variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (cardinal : Nat.card (completeGroup P.family torsion)=4)
variable (noncyclic : ¬IsCyclic (completeGroup P.family torsion))
variable (standard : ClosureKleinCurrent.kind G P torsion cardinal noncyclic=.standard)

include cardinal noncyclic standard in
theorem all_pairs_or_quaternary {n : ℕ} (f : Signature (OI.K G) (2+n)) (positive : 0<n)
    (prime : Prime (⟨2+n,f⟩ : AnySignature (OI.K G))) (actual : Gadget.Realizes P.family .disequality f)
    (r : Signature ℝ (2+n)) (c : ℂ) (hc : c≠0)
    (normal : RH.mapSignature (ClosurePhysicalBridge.complexEmbedding G) f=fun x=>c*(r x:ℂ)) :
    (∀p : Equiv.Perm (Fin (2+n)),N.OrthogonalPair (Tensor.reindex p r)) ∨
      ∃q : Signature (OI.K G) 4,q≠0 ∧ Gadget.Realizes P.family .disequality q ∧
        ¬MatchingOrZero (actualTransfers P.family) q := by
  classical
  by_cases exit : ∃q : Signature (OI.K G) 4,q≠0 ∧ Gadget.Realizes P.family .disequality q ∧
      ¬MatchingOrZero (actualTransfers P.family) q
  · exact Or.inr exit
  · left
    intro p
    have source : Gadget.Realizes P.family .disequality (Tensor.reindex p f) := by
      simpa only [Equiv.symm_symm] using
        Holant.Dihedral.CompatibleClosure.realizes_reindex P.family .disequality f actual p.symm
    have form : RH.mapSignature (ClosurePhysicalBridge.complexEmbedding G) (Tensor.reindex p f)=
        fun x=>c*((Tensor.reindex p r x : ℝ):ℂ) := by
      funext x
      exact congrFun normal (fun i=>x (p i))
    exact (GlobalCloseCompletionKleinGramCurrent.orthogonal_or_quaternary G P torsion cardinal noncyclic
      standard (Tensor.reindex p f) positive (prime_reindex f prime p) source
      (Tensor.reindex p r) c hc form).resolve_right exit


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinGramAllPairs
end
