import Holant.Proofs.Closure.ClosureBStableFamily
import Holant.Proofs.Closure.ClosureStableFactorDescent

/-! Exact original-field higher-arity B split. The fixed binary is literally
one matrix of the internally selected original CURRENT matching presentation.
The B coordinate action is inverted at the SAME ordered partition, then pivot
descent recovers only the residual factor. No new Palette or factor is input. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureBStable
open Holant Holant.Tractable Holant.Algebraic Holant.Marked
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.LocalDrafts.MainChain
open Holant.Dihedral.CompatibleClosure Holant.Dihedral.CompatibleCoefficientLine
open ClosureStableFactor ClosureCompatibleAlignment

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (N : ClosureMarkedDihedralB.NativeB
  (ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G) P.family torsion))

theorem transformed_nonzero {n : ℕ} (f : Signature (OI.K G) n) (nonzero : f≠0) :
    transformed G f≠0 := by
  intro zero
  have recovered := basisB.action_symm_action
    (RingHomRealization.mapSignature (ClosureSourceRows.embedding G) f)
  change basisB.action (transformed G f)=_ at recovered
  rw [zero,ClosureFactorTreeAction.action_zero] at recovered
  apply nonzero
  funext x
  apply (ClosureSourceRows.embedding G).injective
  simpa only [RingHomRealization.mapSignature,map_zero,Pi.zero_apply] using (congrFun recovered x).symm

variable {r : ℕ} (f : Signature (OI.K G) (2*r+4))
variable (order : Equiv.Perm (Fin (2*r+4)))
variable (stable : ∀ g ∈ rawDeck P.family torsion f, MatchingOrZero (actualTransfers P.family) g)

theorem sampleTensor_nonzero (nonzero : f≠0) : sampleTensor G f order≠0 := by
  intro zero
  apply transformed_nonzero G f nonzero
  funext x
  have h := congrFun zero (fun j => x (order j))
  simpa only [sampleTensor,Tensor.reindex,Equiv.apply_symm_apply,Pi.zero_apply] using h

def anchor (nonzero : f≠0) : Sample G P torsion N f order :=
  ClosureBStableFactor.canonicalAnchor N.selected.range (sampleTensor G f order)
    (sampleTensor_nonzero G f order nonzero)

variable (chosen : Sample G P torsion N f order)

def anchorOriginalBinary (e : Fin (r+1)) : Matrix Bool Bool (OI.K G) :=
  (selected G P torsion N f order stable chosen).native.matrix
    ((finCongr (selected G P torsion N f order stable chosen).edgeCount).symm e)

def anchorOriginalTable (e : Fin (r+1)) : Signature (OI.K G) 2 :=
  fun x => anchorOriginalBinary G P torsion N f order stable chosen e (x 0) (x 1)

theorem anchor_transport_exact (e : Fin (r+1)) :
    familyTables G P torsion N f order stable chosen chosen e=
      transport basisB (HistorySectorCards.mapBinary (ClosureSourceRows.embedding G)
        (anchorOriginalBinary G P torsion N f order stable chosen e)) := by
  have self : familyTables G P torsion N f order stable chosen chosen e=
      (selected G P torsion N f order stable chosen).factors e := by
    simp [familyTables,familyPorts,alignedFactor,edgeIndex,edgeReversed]
  rw [self]
  rfl

theorem anchor_transform (e : Fin (r+1)) :
    transformed G (anchorOriginalTable G P torsion N f order stable chosen e)=
      kernelSignature (familyTables G P torsion N f order stable chosen chosen e) := by
  rw [anchor_transport_exact]
  have mapped : RingHomRealization.mapSignature (ClosureSourceRows.embedding G)
      (anchorOriginalTable G P torsion N f order stable chosen e)=
      kernelSignature (HistorySectorCards.mapBinary (ClosureSourceRows.embedding G)
        (anchorOriginalBinary G P torsion N f order stable chosen e)) := rfl
  rw [transformed,mapped]
  exact transport_signature basisB _

theorem anchor_original_nonzero (e : Fin (r+1)) :
    anchorOriginalTable G P torsion N f order stable chosen e≠0 := by
  have nonsingular := groupM_det_nonzero (by have := N.selected.range; omega)
    (family_member G P torsion N f order stable chosen chosen e)
  obtain ⟨b,c,live⟩ := nonsingular_has_entry _ nonsingular
  intro zero
  have h := anchor_transform G P torsion N f order stable chosen e
  rw [zero] at h
  have mapped : RingHomRealization.mapSignature (ClosureSourceRows.embedding G)
      (0 : Signature (OI.K G) 2)=0 := by funext x; exact map_zero _
  rw [transformed,mapped,ClosureFactorTreeAction.action_zero] at h
  have entry := congrFun h (Fin.cons b (Fin.cons c Fin.elim0))
  exact live entry.symm

set_option backward.isDefEq.respectTransparency false in
/-- The original CURRENT anchor table, original ordered port partition and
unit source multiplier are all retained by the higher-arity constructor. -/
theorem current_original_split (large : 2≤r) :
    ∃ e : Fin (r+1), ∃ R : Signature (OI.K G) (2*r+2),
      ∃ result : ProperSplit (⟨2*r+4,f⟩ : AnySignature (OI.K G))
        ⟨2,anchorOriginalTable G P torsion N f order stable chosen e⟩ ⟨2*r+2,R⟩,
      result.ports=(factorPorts (2*r)).trans
        ((ClosureStableFactor.liftResidual
          ((family G P torsion N f order stable chosen large).residualOrder e)).trans order) ∧
      result.scale=1 := by
  let F := family G P torsion N f order stable chosen large
  obtain ⟨e,R,split,ports,unit⟩ := F.split N.selected.range large
  let reordered : ProperSplit (⟨2*r+4,transformed G f⟩ : AnySignature Scalar)
      ⟨2,kernelSignature (familyTables G P torsion N f order stable chosen chosen e)⟩ ⟨2*r+2,R⟩ := {
    left_pos := split.left_pos
    right_pos := split.right_pos
    ports := split.ports.trans order
    scale := split.scale
    equation := by
      funext x
      have h := congrFun split.equation (fun j => x (order j))
      simpa only [F,family,sampleTensor,Tensor.reindex,Equiv.apply_symm_apply,Equiv.trans_apply] using h }
  let acted := ClosureFactorTreeAction.split basisB reordered
  have leftExact : basisB.action
      (kernelSignature (familyTables G P torsion N f order stable chosen chosen e))=
      RingHomRealization.mapSignature (ClosureSourceRows.embedding G)
        (anchorOriginalTable G P torsion N f order stable chosen e) := by
    rw [←anchor_transform G P torsion N f order stable chosen e]
    exact basisB.action_symm_action _
  let originalMapped : ProperSplit
      (mapSignature (ClosureSourceRows.embedding G) (⟨2*r+4,f⟩ : AnySignature (OI.K G)))
      (mapSignature (ClosureSourceRows.embedding G)
        (⟨2,anchorOriginalTable G P torsion N f order stable chosen e⟩ : AnySignature (OI.K G)))
      ⟨2*r+2,basisB.action R⟩ := {
    left_pos := acted.left_pos
    right_pos := acted.right_pos
    ports := acted.ports
    scale := acted.scale
    equation := by
      have h := acted.equation
      simp only [acted,ClosureFactorTreeAction.signature,reordered,transformed,
        InvertibleKernel.action_symm_action,ClosureFactorTreeAction.split_ports,
        ClosureFactorTreeAction.split_scale] at h
      rw [leftExact] at h
      exact h }
  obtain ⟨right,result,exactPorts,exactUnit⟩ := known_left_descends (ClosureSourceRows.embedding G) f
    (anchorOriginalTable G P torsion N f order stable chosen e)
    (anchor_original_nonzero G P torsion N f order stable chosen e) _ originalMapped
  refine ⟨e,right,result,?_,exactUnit⟩
  rw [exactPorts]
  change split.ports.trans order=_
  rw [ports]
  rfl

/-- The anchor and all cards are selected internally from the nonzero actual
source. Primality is not needed to construct this original-field split. -/
theorem current_original_split_of_nonzero (nonzero : f≠0) (large : 2≤r) :
    let chosen := anchor G P torsion N f order nonzero
    ∃ e : Fin (r+1), ∃ R : Signature (OI.K G) (2*r+2),
      ∃ result : ProperSplit (⟨2*r+4,f⟩ : AnySignature (OI.K G))
        ⟨2,anchorOriginalTable G P torsion N f order stable chosen e⟩ ⟨2*r+2,R⟩,
      result.ports=(factorPorts (2*r)).trans
        ((ClosureStableFactor.liftResidual
          ((family G P torsion N f order stable chosen large).residualOrder e)).trans order) ∧
      result.scale=1 :=
  current_original_split G P torsion N f order stable (anchor G P torsion N f order nonzero) large

include P torsion N order stable in
theorem current_nativeB_not_prime (large : 2≤r) : ¬Prime (⟨2*r+4,f⟩ : AnySignature (OI.K G)) := by
  intro prime
  obtain ⟨e,R,split,_,_⟩ := current_original_split_of_nonzero G P torsion N f order stable prime.1 large
  exact prime.2 ⟨_,_,⟨split⟩⟩

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureBStable
