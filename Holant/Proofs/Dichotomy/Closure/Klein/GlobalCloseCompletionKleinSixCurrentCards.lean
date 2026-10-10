import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinSixCardReal
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinSixBellCoordinates
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinGramCurrent
import Holant.Proofs.Closure.ClosureCyclicCurrentScalar

/-! Any actual real-line six-port prime has genuine common-scalar Bell
coordinates or supplies an actual nonmatching quaternary. A missing lower
output is tested and returned internally; no lower-output closure is assumed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinSixCurrentCards
open Holant Holant.Tractable Holant.Algebraic Holant.Marked
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.Projective.BoundedTorsion hiding binarySignature
namespace B
export GlobalCloseCompletionKleinSixBellNorm (card orthogonal_cards)
end B
namespace N
export GlobalCloseCompletionKleinGramNorm (OrthogonalPair)
end N
namespace R
export RingHomRealization (mapSignature)
end R
namespace C
export GlobalCloseCompletionKleinSixBellCoordinates (Normal normal)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
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
theorem coordinates_or_quaternary (f : Signature (OI.K G) 6)
    (actual : Gadget.Realizes P.family .disequality f) (r : Signature ℝ 6) (c : ℂ) (hc : c≠0)
    (normal : R.mapSignature (ClosurePhysicalBridge.complexEmbedding G) f=fun x=>c*(r x:ℂ))
    (orthogonal : N.OrthogonalPair (n:=4) r) :
    Nonempty (C.Normal r) ∨ ∃q : Signature (OI.K G) 4,q≠0 ∧
      Gadget.Realizes P.family .disequality q ∧ ¬MatchingOrZero (actualTransfers P.family) q := by
  classical
  by_cases exit : ∃q : Signature (OI.K G) 4,q≠0 ∧ Gadget.Realizes P.family .disequality q ∧
      ¬MatchingOrZero (actualTransfers P.family) q
  · exact Or.inr exit
  left
  apply C.normal r orthogonal
  obtain ⟨_,_,_,live⟩ := B.orthogonal_cards r orthogonal
  intro k
  let key := ClosureKleinCurrent.cardKey G P torsion cardinal noncyclic (Equiv.refl (Fin 6)) k
  let q : Signature (OI.K G) 4 := rawCard P.family torsion f key
  have actualQ : Gadget.Realizes P.family .disequality q :=
    rawCard_realizes_exact P.family torsion (P.retainsIdentity G) (by norm_num) f actual key
  have matching : MatchingOrZero (actualTransfers P.family) q := by
    by_contra bad
    exact exit ⟨q,fun zero=>bad (Or.inl zero),actualQ,bad⟩
  let qa := R.mapSignature (ClosureSourceRows.embedding G) q
  have mapped := ClosureKleinCurrent.matching_mapped G P torsion cardinal noncyclic q matching
  rw [standard] at mapped
  let d : ℂ := (ClosurePhysicalBridge.complexEmbedding G)
    (ClosureKleinCurrent.dualCorrection G P torsion cardinal noncyclic k)*c/2
  have hd : d≠0 := div_ne_zero
    (mul_ne_zero ((map_ne_zero _).mpr (ClosureKleinCurrent.dualCorrection_nonzero G P torsion cardinal noncyclic k)) hc)
    (by norm_num)
  have equation (x : Fin 4→Bool) : (qa x:ℂ)=d*(B.card r k x:ℂ) :=
    GlobalCloseCompletionKleinSixCardReal.raw G P torsion cardinal noncyclic standard f r c normal k x
  have nonzero : qa≠0 := by
    intro zero
    apply live k
    funext x
    have h := equation x
    rw [zero,Pi.zero_apply,ZeroMemClass.coe_zero] at h
    have hz := (mul_eq_zero.mp h.symm).resolve_left hd
    exact_mod_cast hz
  exact GlobalCloseCompletionKleinSixMatchingCoordinates.real_coordinates qa mapped nonzero (B.card r k) d hd equation

include cardinal noncyclic standard in
theorem from_prime (f : Signature (OI.K G) 6)
    (prime : Prime (⟨6,f⟩ : AnySignature (OI.K G))) (actual : Gadget.Realizes P.family .disequality f)
    (r : Signature ℝ 6) (c : ℂ) (hc : c≠0)
    (normal : R.mapSignature (ClosurePhysicalBridge.complexEmbedding G) f=fun x=>c*(r x:ℂ)) :
    Nonempty (C.Normal r) ∨ ∃q : Signature (OI.K G) 4,q≠0 ∧
      Gadget.Realizes P.family .disequality q ∧ ¬MatchingOrZero (actualTransfers P.family) q := by
  rcases GlobalCloseCompletionKleinGramCurrent.orthogonal_or_quaternary G P torsion cardinal noncyclic
    standard (n:=4) f (by decide) prime actual r c hc normal with orthogonal|quaternary
  · exact coordinates_or_quaternary G P torsion cardinal noncyclic standard f actual r c hc normal orthogonal
  · exact Or.inr quaternary

include cardinal noncyclic standard in
theorem from_upTo (f : Signature (OI.K G) 6)
    (prime : Prime (⟨6,f⟩ : AnySignature (OI.K G))) (actual : Gadget.RealizesUpTo P.family .disequality f)
    (r : Signature ℝ 6) (c : ℂ) (hc : c≠0)
    (normal : R.mapSignature (ClosurePhysicalBridge.complexEmbedding G) f=fun x=>c*(r x:ℂ)) :
    Nonempty (C.Normal r) ∨ ∃q : Signature (OI.K G) 4,q≠0 ∧
      Gadget.Realizes P.family .disequality q ∧ ¬MatchingOrZero (actualTransfers P.family) q := by
  obtain ⟨d,hd,actual⟩ := actual
  let scaled : Signature (OI.K G) 6 := fun x=>d*f x
  have normal' : R.mapSignature (ClosurePhysicalBridge.complexEmbedding G) scaled=
      fun x=>((ClosurePhysicalBridge.complexEmbedding G) d*c)*(r x:ℂ) := by
    funext x
    change (ClosurePhysicalBridge.complexEmbedding G) (d*f x)=_
    rw [map_mul]
    have h := congrFun normal x
    change (ClosurePhysicalBridge.complexEmbedding G) (f x)=c*(r x:ℂ) at h
    rw [h]
    ring
  exact from_prime G P torsion cardinal noncyclic standard scaled
    (ClosureCyclicCurrent.prime_scaled ⟨6,f⟩ prime d hd) actual r
    ((ClosurePhysicalBridge.complexEmbedding G) d*c) (mul_ne_zero ((map_ne_zero _).mpr hd) hc) normal'


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinSixCurrentCards
end
