import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinQuaternaryRestart
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinHigherNonaffineFrontFourier
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinHigherNonaffineFactorRestart
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinHigherNonaffineGramFront

/-! Genuine RM-assisted norm/support producer for an arbitrary current
nonaffine row. A failure of constant coefficient squares on parity sectors
produces an actual q4 or an actual same-arity output whose full factor batch
strictly lowers the retained nonaffine minimum. No transformed primeness or
closure of smaller arbitrary outputs is assumed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffineNormSource
open Holant Holant.Tractable Holant.Algebraic
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.CharacterFlat
open GlobalCloseCompletionKleinHigherNonaffineFourier
open GlobalCloseCompletionKleinHigherNonaffineFrontFourier
namespace O
export GlobalCloseCompletionKleinHigherNonaffineOrthogonalActual (action program_actual)
end O
namespace A
export GlobalCloseCompletionKleinAffineLeaf (IsAffine)
end A
namespace L
export GlobalCloseCompletionRetainedPredicateLeaf (Minimum)
end L
namespace R
export GlobalCloseCompletionRetainedPredicateRestart (finalPalette)
end R
namespace RM
export GlobalCloseCompletionC2RMActual (rm)
end RM
namespace RH
export RingHomRealization (mapSignature)
end RH
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
open scoped BigOperators

variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (cardinal : Nat.card (completeGroup P.family torsion)=4)
variable (noncyclic : ¬IsCyclic (completeGroup P.family torsion))
variable (standard : ClosureKleinCurrent.kind G P torsion cardinal noncyclic=.standard)

abbrev complexEmbedding := ClosurePhysicalBridge.complexEmbedding G

def UniformSquares {n : ℕ} (f : Signature (OI.K G) n) : Prop :=
  ∀x y : BinaryVector n,dot (ones n) x=dot (ones n) y→
    complexEmbedding G (f (wordVector x))^2=complexEmbedding G (f (wordVector y))^2

include cardinal noncyclic standard in
theorem uniform_or_continue {n : ℕ} (positive : 0<n)
    (cRM : OI.K G) (rmNonzero : cRM≠0)
    (rmActual : Gadget.Realizes P.family .disequality (cRM • RM.rm))
    (old : L.Minimum G P (A.IsAffine G))
    (f : Signature (OI.K G) (n+2)) (actual : Gadget.Realizes P.family .disequality f)
    (bad : ¬Affine (RH.mapSignature (ClosureSourceRows.embedding G) f))
    (bound : n+2≤old.signature.1)
    (r : Signature ℝ (n+2)) (c : ℂ) (hc : c≠0)
    (normal : RH.mapSignature (complexEmbedding G) f=fun x=>c*(r x:ℂ)) :
    UniformSquares G f ∨ Nonempty (GlobalCloseCompletionKleinQuaternaryRestart.D.Output G P) ∨
      ∃q : Signature (OI.K G) (n+2),∃nonzero : q≠0,
        ∃actualQ : Gadget.Realizes P.family .disequality q,
        ∃new : L.Minimum G (R.finalPalette G P ⟨n+2,q⟩ nonzero (by change 0<n+2;omega) actualQ) (A.IsAffine G),
          new.signature.1<old.signature.1 := by
  classical
  by_cases uniform : UniformSquares G f
  · exact Or.inl uniform
  right
  let fc := RH.mapSignature (complexEmbedding G) f
  obtain ⟨p,both,witness⟩ := front_fourier_witness (fun x=>fc (wordVector x)^2) uniform
  obtain ⟨q,d,hd,actualQ,equation,affine⟩ := O.program_actual (ClosureSourceRows.embedding G)
    P.family P.equality cRM rmNonzero rmActual f actual p
  have eq : RH.mapSignature (complexEmbedding G) q=d • O.action p fc := equation
  have badQ : ¬A.IsAffine G ⟨n+2,q⟩ := fun h=>bad (affine.mp h)
  have nonzero : q≠0 := by
    intro zero
    apply badQ
    change Affine (RH.mapSignature (ClosureSourceRows.embedding G) q)
    have mapped : RH.mapSignature (ClosureSourceRows.embedding G) q=0 := by
      funext x
      simp [RH.mapSignature,zero]
    rw [mapped]
    exact affine_zero (n+2)
  by_cases prime : Prime (⟨n+2,q⟩ : AnySignature (OI.K G))
  · have normalQ : RH.mapSignature (complexEmbedding G) q=fun x=>(d*c)*((O.action (K:=ℝ) p r x:ℝ):ℂ) := by
      funext x
      change complexEmbedding G (q x)=(d*c)*((O.action (K:=ℝ) p r x:ℝ):ℂ)
      have h := congrFun eq x
      change complexEmbedding G (q x)=d*fc (wordVector (p.inverse.word (vectorWord x))) at h
      rw [h]
      have original := congrFun normal (wordVector (p.inverse.word (vectorWord x)))
      change fc _=c*(_ : ℂ) at original
      rw [original]
      simp only [O.action]
      ring
    rcases GlobalCloseCompletionKleinHigherNonaffineGramFront.orthogonal_or_quaternary
      G P torsion cardinal noncyclic standard positive q prime actualQ (O.action (K:=ℝ) p r) (d*c)
      (mul_ne_zero hd hc) normalQ with gram|quaternary
    · obtain ⟨value,rows⟩ := gram
      have zero := gram_front_zero (RH.mapSignature (complexEmbedding G) q) value rows both
      have squares (x : BinaryVector (n+2)) :
          RH.mapSignature (complexEmbedding G) q (wordVector x)^2=
            d^2*fc (wordVector (p.inverse.word x))^2 := by
        have h := congrFun eq (wordVector x)
        change RH.mapSignature (complexEmbedding G) q (wordVector x)=
          d*fc (wordVector (p.inverse.word (vectorWord (wordVector x)))) at h
        rw [vector_word] at h
        rw [h,mul_pow]
      change (∑x : BinaryVector (n+2),sign (dot (frontMask n both) x)*
        RH.mapSignature (complexEmbedding G) q (wordVector x)^2)=0 at zero
      simp_rw [squares] at zero
      have scale : (∑x : BinaryVector (n+2),sign (dot (frontMask n both) x)*
          (d^2*fc (wordVector (p.inverse.word x))^2))=
          d^2*transform (fun x=>fc (wordVector (p.inverse.word x))^2) (frontMask n both) := by
        rw [transform,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        ring
      rw [scale] at zero
      exact (witness ((mul_eq_zero.mp zero).resolve_left (pow_ne_zero 2 hd))).elim
    · obtain ⟨q4,_live,actual4,nonmatching⟩ := quaternary
      exact Or.inl ⟨⟨q4,actual4,nonmatching⟩⟩
  · right
    obtain ⟨new,smaller⟩ := GlobalCloseCompletionKleinHigherNonaffineFactorRestart.split_strict
      G P ⟨n+2,q⟩ nonzero (by change 0<n+2;omega) actualQ old badQ prime bound
    exact ⟨q,nonzero,actualQ,new,smaller⟩

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffineNormSource
end
