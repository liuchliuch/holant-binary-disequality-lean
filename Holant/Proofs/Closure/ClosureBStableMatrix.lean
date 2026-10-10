import Holant.Proofs.Closure.ClosureMarkedDihedralB
import Holant.Proofs.Closure.HistorySectorCardsAlgebra
import Holant.Dihedral.CompatibleClosure.Monomial

/-! Literal B edge/equality exchange and ordered M phase conventions.
Every edge multiplier and phase inversion is explicit. These matrix identities
do not declare a weighted network native-X or make the basis a gadget. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureBStable
open Holant Holant.Tractable Holant.Marked
open Holant.Dihedral.CompatibleClosure

def edgeScalar : Scalar := -2*imaginaryUnit

theorem edgeScalar_nonzero : edgeScalar≠0 := edgeB_multiplier_ne_zero

theorem edge_exact : sectorEdge basisB=scale edgeScalar Signature.equality := edgeB

theorem inverse_equality : transport basisB Signature.equality=
    scale (imaginaryUnit/2) Signature.disequality := by
  funext a b
  cases a <;> cases b <;>
    simp [transport,basisB,UBInv,Kernel.mul_apply,Kernel.transpose,
      Signature.equality,Signature.disequality,scale] <;>
    ring_nf <;> norm_num [imaginaryUnit_sq]

theorem inverse_disequality : transport basisB Signature.disequality=
    scale (imaginaryUnit/2) Signature.equality := by
  funext a b
  cases a <;> cases b <;>
    simp [transport,basisB,UBInv,Kernel.mul_apply,Kernel.transpose,
      Signature.equality,Signature.disequality,scale] <;>
    ring_nf <;> norm_num [imaginaryUnit_sq]

theorem inverse_equality_signature : basisB.symm.action (kernelSignature Signature.equality)=
    (imaginaryUnit/2) • kernelSignature Signature.disequality := by
  rw [transport_signature,inverse_equality]
  rfl

theorem inverse_disequality_signature : basisB.symm.action (kernelSignature Signature.disequality)=
    (imaginaryUnit/2) • kernelSignature Signature.equality := by
  rw [transport_signature,inverse_disequality]
  rfl

def phaseFor {m : ℕ} (p : Bool) (t : {t : Scalar // Roots m t}) : {t : Scalar // Roots m t} :=
  if p then ⟨t.val⁻¹,t.property.inv⟩ else t

def phaseScalar {m : ℕ} (p : Bool) (t : {t : Scalar // Roots m t}) : Scalar := if p then t.val else 1

theorem phaseScalar_nonzero {m : ℕ} (positive : 0<m) (p : Bool) (t : {t : Scalar // Roots m t}) :
    phaseScalar p t≠0 := by cases p <;> simp [phaseScalar,t.property.ne_zero positive]

/-- The anti-diagonal M convention orders its two nonzero entries oppositely
to S=X R. The genuine inverse phase and nonzero scalar correct that order. -/
theorem phase_order {m : ℕ} (positive : 0<m) (p : Bool) (t : {t : Scalar // Roots m t}) :
    M p t.val=scale (phaseScalar p t)
      (if p then S (phaseFor p t).val else R (phaseFor p t).val) := by
  funext a b
  have tn := t.property.ne_zero positive
  cases p <;> cases a <;> cases b <;>
    simp [phaseFor,phaseScalar,M,monomial,S,R,Kernel.mul_apply,diagonalKernel,
      Signature.equality,Signature.disequality,scale,tn]

theorem effective_kernel (B : Mat) :
    Kernel.mul (Kernel.mul (sectorEdge basisB) (transport basisB B)) (sectorEdge basisB)=
      scale edgeScalar (sectorTransfer basisB B) := by
  rw [Kernel.mul_assoc,transport_mul_edge,edge_exact,scale_mul_left,Kernel.equality_mul]

/-- An exact equality-edge attachment is implemented at an X edge by the
displayed changed binary. No edge multiplier is discarded. -/
def nativeAttachment (C : Mat) : Mat :=
  Kernel.mul (Kernel.mul C (sectorEdge basisB)) Signature.disequality

theorem attachment_kernel (C : Mat) :
    Kernel.mul (nativeAttachment C) Signature.disequality=Kernel.mul C (sectorEdge basisB) := by
  rw [nativeAttachment,Kernel.mul_assoc,Kernel.disequality_mul_disequality,Kernel.mul_equality]

theorem attachment_exact (C : Mat) : nativeAttachment C=scale edgeScalar
    (Kernel.mul C Signature.disequality) := by
  rw [nativeAttachment,edge_exact,scale_mul_right,Kernel.mul_equality,scale_mul_left]

def nativeClosing (C : Mat) : Mat := Kernel.mul
  (Kernel.mul Signature.disequality
    (Kernel.mul (Kernel.mul (sectorEdge basisB) C) (sectorEdge basisB))) Signature.disequality

theorem closing_kernel (C : Mat) : Kernel.mul
    (Kernel.mul Signature.disequality (nativeClosing C)) Signature.disequality=
      Kernel.mul (Kernel.mul (sectorEdge basisB) C) (sectorEdge basisB) := by
  simp only [nativeClosing,Kernel.mul_assoc,Kernel.disequality_mul_disequality,Kernel.mul_equality]
  rw [←Kernel.mul_assoc,Kernel.disequality_mul_disequality,Kernel.equality_mul]

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureBStable
