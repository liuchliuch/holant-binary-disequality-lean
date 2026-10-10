import Holant.Proofs.Dichotomy.Closure.Shifted.GlobalCloseCompletionShiftedQuaternary
import Holant.Certificates.EqualityQuaternary.CoordinatePrimality
import Holant.Marked.SupportAtlas.Source

/-! Full dressed-current safety for the actual shifted mask. Every physical
card is the original raw key with that same mask, permutation and closing
representative. No undressed-deck shortcut or new stability premise is used. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionShiftedMask
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity Holant.Marked
open Holant.Marked.SupportAtlas Holant.Certificates.EqualityQuaternary
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.OpenNetworkComposition
namespace Q
export GlobalCloseCompletionShiftedQuaternary (basis selected parameters)
end Q
namespace H
export HistorySectorNormalized (phaseIndex representatives markedRepresentatives flipDelta flipKey)
end H
namespace C
export ClosureSourceRows (ambientFamily sourceCard_raw representative core_ambient_prime)
end C
namespace RH
export RingHomRealization (mapSignature)
end RH
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (native : GlobalCloseCompletionShiftedMarking.Native G P torsion)
abbrev basis := Q.basis G P torsion native
abbrev selected := Q.selected G P torsion native
abbrev parameters := Q.parameters G P torsion native
abbrev phi := ClosurePhysicalBridge.algebraicEmbedding G
abbrev reps := H.markedRepresentatives G P torsion (basis G P torsion native)
  (selected G P torsion native) (parameters G P torsion native) rfl
variable (q : Signature (OI.K G) 4) (core : MinimumCore P.family)
variable (literal : core.signature=⟨4,q⟩)
variable (stable : ∀f∈rawDeck P.family torsion q,MatchingOrZero (actualTransfers P.family) f)

abbrev ambient := RH.mapSignature (phi G) q
abbrev normalized := (basis G P torsion native).symm.action (ambient G q)
abbrev Delta := Fin 4→Option (completeGroup P.family torsion × Bool)
def originalMask (mask : Word) : Signature (OI.K G) 4 := dress P.family torsion q
  (H.flipDelta G P torsion (basis G P torsion native) (selected G P torsion native) mask)

include core literal in
theorem originalMask_actual (mask : Word) : Gadget.Realizes P.family .disequality
    (originalMask G P torsion native q mask) :=
  dress_actual P.family torsion q
    (Gadget.realizes_of_mem P.family .disequality q (literal ▸ core.retained)) _

include core literal stable in
theorem raw_zero_or_actual (key : RawCardKey 2 (completeGroup P.family torsion)) :
    rawCard P.family torsion q key=0 ∨
      ActualNonsingular P.family (binaryMatrix (rawCard P.family torsion q key)) := by
  rcases ClosureSourceRows.matching_binary_zero_or_nonsingular (actualTransfers P.family)
    (actualTransfers_projectiveMatrixGroup P.family (actualTransfers_nonempty P.family) torsion)
    (rawCard P.family torsion q key) (stable _ (.inr ⟨key,rfl⟩)) with zero|nonsingular
  · exact Or.inl zero
  · refine Or.inr ⟨?_,nonsingular⟩
    change Gadget.Realizes P.family .disequality
      (Holant.Projective.BoundedTorsion.binarySignature (binaryMatrix (rawCard P.family torsion q key)))
    rw [binarySignature_binaryMatrix]
    exact (deckRawDirect G P torsion q core literal key).realizes

theorem physical_raw (delta : Delta G P torsion) (e : Equiv.Perm (Fin 4))
    (p : Bool) (t : Phase (selected G P torsion native).m) :
    physicalCard (RH.mapSignature (phi G) (dress P.family torsion q delta)) e
      ((reps G P torsion native).matrix p t)=
      (binaryMatrix (rawCard P.family torsion q
        (delta,e,(H.phaseIndex G P torsion (basis G P torsion native)
          (selected G P torsion native) p t).key,false))).map (phi G) := by
  have h := C.sourceCard_raw G P torsion (dress P.family torsion q delta) e
    (H.phaseIndex G P torsion (basis G P torsion native) (selected G P torsion native) p t).key
  simpa only [rawCard,ClosureSourceRows.orderedKey,orientBinary,Bool.false_eq_true,
    ite_false,ClosureSourceRows.dress_none,reps,HistorySectorNormalized.markedRepresentatives,
    HistorySectorNormalized.representatives,phi,ClosurePhysicalBridge.algebraicEmbedding,
    ClosureSourceRows.embedding] using h

include core literal stable in
theorem dressed_physical (delta : Delta G P torsion) :
    PhysicalDeck (C.ambientFamily G P) (parameters G P torsion native)
      (RH.mapSignature (phi G) (dress P.family torsion q delta)) (reps G P torsion native) := by
  intro e p t
  change physicalCard _ e ((reps G P torsion native).matrix p t)=0 ∨
    sectorTransfer (basis G P torsion native)
      (physicalCard _ e ((reps G P torsion native).matrix p t))∈groupM (selected G P torsion native).m
  let key : RawCardKey 2 (completeGroup P.family torsion) :=
    (delta,e,(H.phaseIndex G P torsion (basis G P torsion native)
      (selected G P torsion native) p t).key,false)
  rcases raw_zero_or_actual G P torsion q core literal stable key with zero|actual
  · left
    rw [physical_raw]
    change (binaryMatrix (rawCard P.family torsion q key)).map (phi G)=0
    rw [zero]
    ext a b
    simp [binaryMatrix]
  · right
    rw [physical_raw]
    exact ClosureMarkedDihedralCoordinates.Source.actual_sector_spectrum
      (basis G P torsion native) (phi G) P.family torsion (selected G P torsion native)
      (binaryMatrix (rawCard P.family torsion q key)) actual

include core literal stable in
theorem dressed_safe (delta : Delta G P torsion) :
    SafeDeck (selected G P torsion native).m (Holant.Marked.SupportAtlas.delta (parameters G P torsion native) : ℂ)
      (complexTensor ((basis G P torsion native).symm.action
        (RH.mapSignature (phi G) (dress P.family torsion q delta)))) :=
  safeDeck_of_physical (C.ambientFamily G P) (parameters G P torsion native) (by trivial)
    _ (reps G P torsion native) (dressed_physical G P torsion native q core literal stable delta)

theorem map_splice {L : Type} [Field L] (phi : L→+*AlgebraicComplex)
    (f : Signature L 4) (B : Binary (K:=L)) (i : Fin 4) :
    RH.mapSignature phi (spliceTensor f (Holant.Projective.BoundedTorsion.binarySignature B) i)=
      spliceTensor (RH.mapSignature phi f) (kernelSignature (B.map phi)) i := by
  funext x
  simp only [RH.mapSignature,spliceTensor,map_sum,map_mul,
    Holant.Projective.BoundedTorsion.binarySignature,kernelSignature,Matrix.map_apply]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  cases u <;> cases v <;> simp [Signature.disequality]

theorem originalMask_map (mask : Word) : RH.mapSignature (phi G) (originalMask G P torsion native q mask)=
    dressMask (ambient G q) ((reps G P torsion native).matrix true (phaseOne (selected G P torsion native).m)) mask := by
  let key := H.flipKey G P torsion (basis G P torsion native) (selected G P torsion native)
  have step (f : Signature (OI.K G) 4) (i : Fin 4) :
      RH.mapSignature (phi G)
        (Holant.LocalDrafts.FinitePGL2.Stabilization.dressAt P.family torsion f
          (fun j=>if mask j then some (key,false) else none) i)=
      Holant.Marked.SupportAtlas.dressAt (RH.mapSignature (phi G) f)
        ((reps G P torsion native).matrix true (phaseOne (selected G P torsion native).m)) mask i := by
    cases h : mask i
    · simp only [Holant.LocalDrafts.FinitePGL2.Stabilization.dressAt,
        Holant.Marked.SupportAtlas.dressAt,h,Bool.false_eq_true,ite_false]
    · simp only [Holant.LocalDrafts.FinitePGL2.Stabilization.dressAt,h,ite_true,orientBinary,Bool.false_eq_true,ite_false]
      rw [map_splice]
      change spliceTensor _ _ i=Holant.Marked.SupportAtlas.dressAt _ _ mask i
      rw [Holant.Marked.SupportAtlas.dressAt,h]
      exact (Holant.Projective.CyclicDressing.onePort_eq_splice _ _ i).symm
  unfold originalMask dress dressMask
  change RH.mapSignature (phi G) ((List.finRange 4).foldl
    (fun f i=>Holant.LocalDrafts.FinitePGL2.Stabilization.dressAt P.family torsion f
      (fun j=>if mask j then some (key,false) else none) i) q)=_
  simp only [show List.finRange 4=[0,1,2,3] from rfl,List.foldl_cons,List.foldl_nil]
  rw [step,step,step,step]

include core literal in
theorem normalized_prime : TensorPrime (normalized G P torsion native q) :=
  prime_coordinateAction (C.core_ambient_prime G P q core literal)
    (fun _=>(basis G P torsion native).inverse) (fun _=>(basis G P torsion native).matrix)
    (fun _=>(basis G P torsion native).matrix_inverse)

include core literal in
theorem masked_prime (mask : Word) : TensorPrime ((basis G P torsion native).symm.action
    (RH.mapSignature (phi G) (originalMask G P torsion native q mask))) := by
  rw [originalMask_map]
  have he : (basis G P torsion native).symm.action (dressMask (ambient G q)
      ((reps G P torsion native).matrix true (phaseOne (selected G P torsion native).m)) mask)=
      dressingMultiplier ((reps G P torsion native).multiplier true (phaseOne (selected G P torsion native).m)) mask •
        Flip.value (normalized G P torsion native q) mask := by
    funext x
    exact sector_dressMask _ _ _ _ (reps G P torsion native).x_transfer mask x
  rw [he]
  exact prime_smul (flip_prime (normalized_prime G P torsion native q core literal) mask) _
    (dressingMultiplier_ne_zero _ ((reps G P torsion native).multiplier_ne_zero _ _) mask)

include core literal stable in
theorem atlas : ∃mask : Word,ComplementForm ((basis G P torsion native).symm.action
    (RH.mapSignature (phi G) (originalMask G P torsion native q mask))) := by
  obtain ⟨mask,_actual,_nonzero,_value,form⟩ := source_marked_support_atlas
    (C.ambientFamily G P) (parameters G P torsion native) (by trivial) (ambient G q)
    (C.core_ambient_prime G P q core literal).1
    (RingHomRealization.realizes_map (phi G)
      (Gadget.realizes_of_mem P.family .disequality q (literal ▸ core.retained)))
    (reps G P torsion native)
    ((nativePhysicalDeck_iff _ _ _ _).mpr
      (HistorySectorNormalized.markedPhysicalDeck G P torsion (basis G P torsion native)
        (selected G P torsion native) (parameters G P torsion native) rfl q core literal stable))
  exact ⟨mask,by rw [originalMask_map]; exact form⟩


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionShiftedMask
end
