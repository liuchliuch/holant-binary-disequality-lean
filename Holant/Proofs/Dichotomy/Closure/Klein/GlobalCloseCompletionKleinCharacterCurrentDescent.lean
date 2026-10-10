import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinCharacterDescent
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinCharacterCurrentResources
import Holant.Proofs.Dichotomy.Closure.Retained.GlobalCloseCompletionRetainedCharacterLeaf
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinH6RMOriginal

/-! Actual standard-Pauli family descent and full retained-factor restart.
The RM scalar is an actual original-field resource; the H6 entry constructs it
from the checked source circuit. The result remains in the unchanged original
family before its complete retained augmentation is processed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinCharacterCurrentDescent
open Holant Holant.Tractable Holant.Algebraic Holant.Marked
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.ReedMuller.CharacterFlat
namespace C
export GlobalCloseCompletionKleinCharacterCurrentResources (bell_actual)
end C
namespace D
export GlobalCloseCompletionKleinCharacterDescent (smaller_noncharacter small_or_odd)
end D
namespace R
export GlobalCloseCompletionC2RMActual (rm)
end R
namespace L
export GlobalCloseCompletionRetainedCharacterLeaf (Predicate zeroary exists_strict_minimum)
end L
namespace S
export GlobalCloseCompletionRetainedPredicateRestart (finalPalette)
end S
namespace M
export GlobalCloseCompletionRetainedPredicateLeaf (Minimum)
end M
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
variable (c : OI.K G) (hc : c≠0) (rmActual : Gadget.Realizes P.family .disequality (c • R.rm))

theorem bad_nonzero_positive (q : AnySignature (OI.K G)) (bad : ¬L.Predicate G q) :
    q.2≠0 ∧ 0<q.1 := by
  constructor
  · intro zero
    apply bad
    left
    funext x
    simp [RingHomRealization.mapSignature,zero]
  · by_contra h
    obtain ⟨n,f⟩ := q
    have hn : n=0 := by simp only at h;omega
    subst n
    exact bad (L.zeroary _)

include cardinal noncyclic standard hc rmActual in
theorem smaller {n : ℕ} (f : Signature (OI.K G) (n+2)) (actual : Gadget.Realizes P.family .disequality f)
    (large : 10≤n+2) (even : Even (n+2)) (bad : ¬L.Predicate G ⟨n+2,f⟩) :
    ∃q : AnySignature (OI.K G),q.1<n+2 ∧ q.2≠0 ∧ 0<q.1 ∧
      Gadget.Realizes P.family .disequality q.2 ∧ ¬L.Predicate G q := by
  obtain ⟨m,q,hm,actualQ,badQ⟩ := D.smaller_noncharacter (ClosureSourceRows.embedding G) P.family
    (C.bell_actual G P torsion cardinal noncyclic standard) c hc rmActual f actual large even bad
  have live := bad_nonzero_positive G ⟨m,q⟩ badQ
  exact ⟨⟨m,q⟩,hm,live.1,live.2,actualQ,badQ⟩

include cardinal noncyclic standard hc rmActual in
theorem small_or_odd {n : ℕ} (f : Signature (OI.K G) n) (actual : Gadget.Realizes P.family .disequality f)
    (bad : ¬L.Predicate G ⟨n,f⟩) :
    ∃q : AnySignature (OI.K G),(q.1≤8 ∨ Odd q.1) ∧ q.2≠0 ∧ 0<q.1 ∧
      Gadget.Realizes P.family .disequality q.2 ∧ ¬L.Predicate G q := by
  obtain ⟨m,q,hm,actualQ,badQ⟩ := D.small_or_odd (ClosureSourceRows.embedding G) P.family
    (C.bell_actual G P torsion cardinal noncyclic standard) c hc rmActual f actual bad
  have live := bad_nonzero_positive G ⟨m,q⟩ badQ
  exact ⟨⟨m,q⟩,hm,live.1,live.2,actualQ,badQ⟩

include cardinal noncyclic standard hc rmActual in
theorem restart {n : ℕ} (f : Signature (OI.K G) (n+2)) (actual : Gadget.Realizes P.family .disequality f)
    (old : M.Minimum G P (L.Predicate G)) (literal : old.signature=⟨n+2,f⟩)
    (large : 10≤n+2) (even : Even (n+2)) :
    ∃q : AnySignature (OI.K G),∃nonzero : q.2≠0,∃positive : 0<q.1,
      ∃actualQ : Gadget.Realizes P.family .disequality q.2,
      ∃new : M.Minimum G (S.finalPalette G P q nonzero positive actualQ) (L.Predicate G),
        new.signature.1<old.signature.1 := by
  have bad : ¬L.Predicate G ⟨n+2,f⟩ := by simpa only [literal] using old.bad
  obtain ⟨q,smaller,nonzero,positive,actualQ,badQ⟩ :=
    smaller G P torsion cardinal noncyclic standard c hc rmActual f actual large even bad
  obtain ⟨new,hn⟩ := L.exists_strict_minimum G P q nonzero positive actualQ badQ old
    (by simpa only [literal] using smaller)
  exact ⟨q,nonzero,positive,actualQ,new,hn⟩

include cardinal noncyclic standard in
theorem from_h6 {n : ℕ} (h : Signature (OI.K G) 6) (actualH : Gadget.Realizes P.family .disequality h)
    (scale : ℂ) (scale_ne : scale≠0)
    (normal : RingHomRealization.mapSignature (ClosurePhysicalBridge.complexEmbedding G) h=
      scale • Holant.ReedMuller.CharacterFlat.hCore)
    (f : Signature (OI.K G) n) (actualF : Gadget.Realizes P.family .disequality f)
    (bad : ¬L.Predicate G ⟨n,f⟩) :
    ∃q : AnySignature (OI.K G),(q.1≤8 ∨ Odd q.1) ∧ q.2≠0 ∧ 0<q.1 ∧
      Gadget.Realizes P.family .disequality q.2 ∧ ¬L.Predicate G q := by
  obtain ⟨d,hd,rm⟩ := GlobalCloseCompletionKleinH6RMOriginal.current_actual G P h actualH scale scale_ne normal
  exact small_or_odd G P torsion cardinal noncyclic standard d hd rm f actualF bad


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinCharacterCurrentDescent
end
