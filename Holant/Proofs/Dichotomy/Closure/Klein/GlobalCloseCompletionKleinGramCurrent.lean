import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinGramNorm
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinGramTransport
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinStandardRealLine

/-! The norm-stage producer in the actual standard-Pauli current family.
A real-line prime either obeys selected-pair orthogonality or supplies a genuine
nonmatching quaternary over the unchanged original field and source. Its full
two-copy graph and every scalar are retained; no q4 closure is assumed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinGramCurrent
open Holant Holant.Tractable Holant.Algebraic Holant.Marked
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.Projective.BoundedTorsion hiding binarySignature
namespace A
export GlobalCloseCompletionKleinGramActual (gram actual)
end A
namespace N
export GlobalCloseCompletionKleinGramNorm (OrthogonalPair orthogonal_or_split)
end N
namespace T
export GlobalCloseCompletionKleinGramTransport (real_gram real_split_descends)
end T
namespace RH
export RingHomRealization (mapSignature)
end RH
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (cardinal : Nat.card (completeGroup P.family torsion)=4)
variable (noncyclic : ¬IsCyclic (completeGroup P.family torsion))
variable (standard : ClosureKleinCurrent.kind G P torsion cardinal noncyclic=.standard)

include cardinal noncyclic standard in
theorem orthogonal_or_quaternary {n : ℕ} (f : Signature (OI.K G) (2+n)) (positive : 0<n)
    (prime : Prime (⟨2+n,f⟩ : AnySignature (OI.K G))) (actual : Gadget.Realizes P.family .disequality f)
    (r : Signature ℝ (2+n)) (c : ℂ) (hc : c≠0)
    (normal : RH.mapSignature (ClosurePhysicalBridge.complexEmbedding G) f=fun x=>c*(r x:ℂ)) :
    N.OrthogonalPair r ∨ ∃q : Signature (OI.K G) 4,q≠0 ∧
      Gadget.Realizes P.family .disequality q ∧ ¬MatchingOrZero (actualTransfers P.family) q := by
  let phi := ClosurePhysicalBridge.complexEmbedding G
  have live : r≠0 := by
    intro zero
    apply prime.1
    funext x
    apply phi.injective
    have h := congrFun normal x
    simpa only [RH.mapSignature,zero,Pi.zero_apply,Complex.ofReal_zero,mul_zero,map_zero] using h
  obtain ⟨d,hd,actualQ⟩ := A.actual P.family P.equality f actual
  let q : Signature (OI.K G) 4 := fun x=>d*A.gram f x
  by_cases matching : MatchingOrZero (actualTransfers P.family) q
  · have canonical := ClosureKleinCurrent.matching_mapped G P torsion cardinal noncyclic q matching
    rw [standard] at canonical
    have coefficient : phi d*c^2≠0 := mul_ne_zero ((map_ne_zero phi).mpr hd) (pow_ne_zero 2 hc)
    have equation (x : Fin 4→Bool) :
        (RH.mapSignature (ClosureSourceRows.embedding G) q x:ℂ)=
          (phi d*c^2)*(A.gram (K:=ℝ) r x:ℂ) := by
      change phi (d*A.gram f x)=(phi d*c^2)*(A.gram (K:=ℝ) r x:ℂ)
      have h := congrFun (T.real_gram phi f r c normal) x
      change phi (A.gram f x)=c^2*(A.gram (K:=ℝ) r x:ℂ) at h
      rw [map_mul,h]
      ring
    rcases N.orthogonal_or_split r live positive _ canonical _ coefficient equation with orthogonal|split
    · exact Or.inl orthogonal
    · obtain ⟨a,b,⟨split⟩⟩ := split
      exact (prime.2 (T.real_split_descends phi f prime.1 r c hc normal split)).elim
  · right
    have nonzero : q≠0 := fun zero=>matching (Or.inl zero)
    exact ⟨q,nonzero,actualQ,matching⟩

include cardinal noncyclic standard in
theorem from_real_line {n : ℕ} (f : Signature (OI.K G) (2+n)) (positive : 0<n)
    (prime : Prime (⟨2+n,f⟩ : AnySignature (OI.K G))) (actual : Gadget.Realizes P.family .disequality f)
    (realLine : Holant.Pauli.ProjectiveDetermination.IsRealLine
      (RH.mapSignature (ClosurePhysicalBridge.complexEmbedding G) f)) :
    ∃r : Signature ℝ (2+n),∃c : ℂ,c≠0 ∧
      RH.mapSignature (ClosurePhysicalBridge.complexEmbedding G) f=(fun x=>c*(r x:ℂ)) ∧
      (N.OrthogonalPair r ∨ ∃q : Signature (OI.K G) 4,q≠0 ∧
        Gadget.Realizes P.family .disequality q ∧ ¬MatchingOrZero (actualTransfers P.family) q) := by
  obtain ⟨c,hc,r,normal⟩ := realLine
  exact ⟨r,c,hc,normal,orthogonal_or_quaternary G P torsion cardinal noncyclic standard
    f positive prime actual r c hc normal⟩


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinGramCurrent
end
