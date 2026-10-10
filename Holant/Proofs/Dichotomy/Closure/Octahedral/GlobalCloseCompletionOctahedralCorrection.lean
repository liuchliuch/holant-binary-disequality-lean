import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralPrototype

/-! Coefficient extraction from the preserved marked-octahedral proof. Actual old representative lookup for the prototype
correction. Three identity slots and the single fourth-slot group action
are all physically realized by OLD saved binaries and native-X splices.
The local prototype comparison is produced by Source, never an input to
the public classifier. The following PGL base terminal is a fourth stage. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankTwo.CanonicalEndpointBridge
open Holant Holant.Algebraic Holant.Projective.BoundedTorsion
open Holant.Certificates Holant.Certificates.OctahedralSeparator
open Holant.Certificates.MatchingContractionClosure Holant.Certificates.TetrahedralPreservers
open Holant.LocalDrafts.MainChain RingHomRealization
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry
open Preserver RankTwo.PhysicalOrbit RankTwo.HarmonicProjectivities RankTwo.BaseTerminals
open scoped Matrix BigOperators

def correctionCodes (f : Form) : Fin 4 → Fin 24 := ![0,0,0,xConjugateIndex f 1]
def correctionReverse : Fin 4 → Bool := ![false,false,false,true]
def correctionSlotScale (f : Form) : Fin 4 → ℂ :=
  ![1,1,1,embed (-imag)*embed (xConjugateScale f 1)]

theorem correctionSlotScale_ne (f : Form) (i : Fin 4) : correctionSlotScale f i ≠ 0 := by
  fin_cases i
  · exact one_ne_zero
  · exact one_ne_zero
  · exact one_ne_zero
  · exact mul_ne_zero (embed_ne_zero (by decide +kernel : (-imag : Scalar) ≠ 0))
      (xConjugateScale_ne f 1)

theorem correction_slots (f : Form) :
    (fun i => complexMatrix (correctionPorts f i)) = fun i => correctionSlotScale f i •
      (if correctionReverse i then (kernel f (correctionCodes f i)).transpose
        else kernel f (correctionCodes f i)) := by
  funext i
  fin_cases i
  · change complexMatrix (q 0) = 1 • kernel f 0
    rw [complexMatrix_q0,kernel_zero,one_smul]
  · change complexMatrix (q 0) = 1 • kernel f 0
    rw [complexMatrix_q0,kernel_zero,one_smul]
  · change complexMatrix (q 0) = 1 • kernel f 0
    rw [complexMatrix_q0,kernel_zero,one_smul]
  · simp only [correctionPorts,correctionSlotScale,correctionReverse,correctionCodes,
      Matrix.cons_val_succ',Matrix.cons_val_zero',ite_true]
    have hx : complexMatrix flip = Holant.Certificates.MatchingContractionClosure.X := complexMatrix_flip
    have hk : complexMatrix (theta f (OctahedralSeparator.standard 1)) = kernel f 1 := rfl
    rw [complexMatrix_mt,complexMatrix_mm,complexMatrix_mm,complexMatrix_ms,hx,hk]
    rw [Matrix.mul_smul,Matrix.smul_mul,xConjugate_kernel,smul_smul,Matrix.transpose_smul]


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankTwo.CanonicalEndpointBridge

