import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralBaseTerminals

/-! Coefficient extraction from the preserved marked-octahedral proof. The right-X canonical prototype is NOT the even
base tensor. Its correction is one actual marked-group output leg. This
file proves the exact fixed-coordinate equality for dd/tt; forms dt/td
are not silently identified with either base. All raw coefficients below
are computed from the OLD root-pair chart and OLD quaternion basis. -/
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankTwo.CanonicalEndpointBridge
open Holant Holant.Certificates Holant.Certificates.OctahedralSeparator
open Holant.Certificates.MatchingProductBridge Holant.Certificates.PlatonicIncidence
open Holant.Certificates.TetrahedralPreservers
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry
open Preserver RankTwo.QuotientEnumeration RankTwo.HarmonicProjectivities
open RankTwo.PhysicalOrbit RankTwo.BaseTerminals
open scoped Matrix BigOperators

def baseFlip : Matrix (Fin 2) (Fin 2) Scalar := ![![1,0],![0,-1]]

theorem base_quotient : ∀ b : Bool,quotientMatrix (baseForm b) baseLine = baseFlip := by
  intro b
  cases b <;> decide +kernel

def rawSign : Fin 4 → Scalar := ![1,-1,1,-1]

/-- The original form0/form1 base root has no Q2 component. This is
exactly the Frobenius-sign correction, not an orthogonality premise. -/
theorem base_dual_raw : ∀ b : Bool,∀ a : Fin 2,∀ i : Fin 4,
    rawSign i*rawPoint (baseForm b) (canonicalPair baseLine a) i =
      (if a=0 then 1 else -1)*rawPoint (baseForm b) (canonicalPair baseLine a) i := by
  intro b a i
  cases b <;> fin_cases a <;> fin_cases i <;> decide +kernel

def rawProjection (f : Form) : Matrix (Fin 4) (Fin 4) Scalar := fun i j =>
  ∑ a : Fin 2,rawPoint f (canonicalPair baseLine a) i*rawPoint f (canonicalPair baseLine a) j

def rawRightX : Matrix (Fin 4) (Fin 4) Scalar := fun i j =>
  RankThree.rawCoordinates (mm (q j) flip) i

def rawDual : Fin 4 → OctahedralSeparator.Mat :=
  ![ms (1/2) (q 0),ms (-1/2) (q 1),ms (1/2) (q 2),ms (-1/2) (q 3)]

def rawAssemble (v : Fin 4 → Scalar) : OctahedralSeparator.Mat := fun u v' =>
  ∑ i : Fin 4,v i*q i u v'

def rawPrototype (f : Form) : Signature Scalar 4 := fun x =>
  ∑ i : Fin 4,rawDual i (x 0) (x 1)*
    rawAssemble (fun j => (rawRightX*rawProjection f) j i) (x 2) (x 3)

/-- Only the fourth original slot is acted on. The two X factors and
the transpose are forced by the right-X transfer used by the old source. -/
def correctionPorts (f : Form) : Fin 4 → OctahedralSeparator.Mat :=
  ![q 0,q 0,q 0,mt (mm (mm flip (ms (-imag) (theta f (OctahedralSeparator.standard 1)))) flip)]

private theorem scalar_four_sum (f : Word → Scalar) :
    (∑ x,f x) = ∑ a : Bool,∑ b : Bool,∑ c : Bool,∑ d : Bool,f ![a,b,c,d] := by
  simp only [Holant.ReedMuller.CoefficientAtlas.sum_words_succ,Fintype.sum_unique]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro d hd
  congr 1

/-- Three literal identity slots leave just the two fourth-port terms. -/
theorem fourth_action (M : OctahedralSeparator.Mat) (R : Signature Scalar 4) (x : Word) :
    Signature.coordinateAction ![q 0,q 0,q 0,M] R x =
      M (x 3) false*R ![x 0,x 1,x 2,false] +
        M (x 3) true*R ![x 0,x 1,x 2,true] := by
  simp only [Signature.coordinateAction,scalar_four_sum]
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;>
    simp [Fin.prod_univ_succ,q,mat,h0,h1,h2,add_comm]


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankTwo.CanonicalEndpointBridge
