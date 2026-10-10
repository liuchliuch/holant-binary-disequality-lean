import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralCorrection

/-! Coefficient extraction from the preserved marked-octahedral proof. The two actual mixed baseline charts, not a
transport of dd/tt terminals. Only the old marked palette is attached.
The quotient charts are evaluated from the old canonical pair and order.
The sixteen coefficients retain the original four ordered positions. -/
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankTwo.MixedEndpointBridge
open Holant Holant.Algebraic Holant.Certificates Holant.Certificates.OctahedralSeparator
open Holant.LocalDrafts.MainChain
open Holant.Certificates.TetrahedralPreservers
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry
open Preserver RankTwo.QuotientEnumeration RankTwo.HarmonicProjectivities
open RankTwo.PhysicalOrbit RankTwo.CanonicalEndpointBridge
open scoped Matrix BigOperators

def mixedRow (b : Bool) : Form := if b then 3 else 2
def smallInverse (b : Bool) : RawSmallMatrix := if b then 1 else baseFlip

/-- The old quotient-order computation gives different baseline charts:
dt has diag(1,-1), whereas td has the identity chart. -/
theorem mixed_quotient : ∀ b : Bool,
    quotientMatrix (mixedRow b) baseLine = smallInverse b := by
  intro b
  cases b <;> decide +kernel

def rawModel (b : Bool) : Matrix (Fin 4) (Fin 4) Scalar := fun i j =>
  ∑ a : Fin 2,∑ c : Fin 2,
    rawPoint (mixedRow b) (canonicalPair baseLine a) i * smallInverse b a c *
      rawSign j * rawPoint (mixedRow b) (canonicalPair baseLine c) j

def rawReconstructed (b : Bool) : Signature Scalar 4 := fun x =>
  ∑ i : Fin 4,rawDual i (x 0) (x 1)*
    rawAssemble (fun j => (rawRightX*rawModel b) j i) (x 2) (x 3)

/-- A short coefficient formula for the actual right-X prototype. The
sign differs between the two mixed forms because their J charts differ. -/
def prototype (b : Bool) : Signature Scalar 4 := fun x =>
  (1/2 : Scalar) *
    (q 0 (x 0) (x 1)*flip (x 2) (x 3) +
      (if b then 1 else -1) * theta (mixedRow b) (q 1) (x 0) (x 1) *
        mm (theta (mixedRow b) (q 1)) flip (x 2) (x 3))

def mixedCodes (b : Bool) : Fin 4 → Fin 24 :=
  if b then ![17,16,0,xConjugateIndex 3 1] else correctionCodes 2

theorem mixedCodes_table : ∀ b : Bool,
    mixedCodes b = if b then ![17,16,0,2] else ![0,0,0,1] := by
  intro b
  cases b <;> decide +kernel

/-- td's two diagonal legs are original palette entries 17 and 16.
The fourth leg is the old reversed correction, in both forms. -/
def mixedPorts (b : Bool) : Fin 4 → Mat :=
  if b then ![theta 3 (OctahedralSeparator.standard 17),
    theta 3 (OctahedralSeparator.standard 16),q 0,correctionPorts 3 3]
  else correctionPorts 2

def cachedMixedPorts (b : Bool) : Fin 4 → OctahedralSeparator.Mat :=
  ![mat (if b then 1-imag else 1) 0 0 (if b then 1+imag else 1),
    mat (if b then 1+imag else 1) 0 0 (if b then 1-imag else 1),q 0,
    mat 0 (if b then coeff 0 (1/2) 0 (-1/2) else 1)
      (if b then coeff 0 (1/2) 0 (1/2) else 1) 0]

theorem mixedPorts_exact (b : Bool) : mixedPorts b = cachedMixedPorts b := by
  funext j u v
  cases b <;> fin_cases j <;> cases u <;> cases v <;> decide +kernel

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

theorem diagonal_fourth_action (a c d e : Scalar) (M : OctahedralSeparator.Mat)
    (R : Signature Scalar 4) (x : Word) :
    Signature.coordinateAction ![mat a 0 0 c,mat d 0 0 e,q 0,M] R x =
      (if x 0 then c else a)*(if x 1 then e else d)*
        (M (x 3) false*R ![x 0,x 1,x 2,false] +
          M (x 3) true*R ![x 0,x 1,x 2,true]) := by
  simp only [Signature.coordinateAction,scalar_four_sum]
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;>
    simp [Fin.prod_univ_succ,q,mat,h0,h1,h2] <;> ring

def phaseWord (x : Word) : Bool :=
  (!(x 0) && (x 1 || x 2 || x 3)) || (x 0 && x 1 && x 2 && x 3)

/-- Lexicographic even entries are (1,1,1,1,1,1,1,1) for dt,
and (1,z,z,z,1,1,1,z) for td. z is later recovered in ORIGINAL L. -/
def mixedShape {K : Type*} [Field K] (b : Bool) (z : K) : Signature K 4 := fun x =>
  if Holant.Marked.SupportAtlas.parity x then 0 else if b && phaseWord x then z else 1

def exteriorScale (b : Bool) : Scalar := if b then (1-imag)/OctahedralSeparator.root else 1/2
def phaseValue {K : Type*} [Field K] (b : Bool) (z : K) : K := if b then z else 1
def phaseProbe : Word := ![false,false,true,true]

/-- FULL sixteen-entry certificate; no target tensor is supplied. -/
theorem exteriorScale_ne (b : Bool) : exteriorScale b ≠ 0 := by
  cases b <;> decide +kernel

theorem shape_zero {K : Type*} [Field K] (b : Bool) (z : K) :
    mixedShape b z (fun _ => false) = 1 := by
  cases b <;> simp [mixedShape,phaseWord,Holant.Marked.SupportAtlas.parity]

theorem shape_one {K : Type*} [Field K] (b : Bool) (z : K) :
    mixedShape b z (fun _ => true) = phaseValue b z := by
  cases b <;> simp [mixedShape,phaseWord,phaseValue,Holant.Marked.SupportAtlas.parity]

theorem shape_probe {K : Type*} [Field K] (b : Bool) (z : K) :
    mixedShape b z phaseProbe = phaseValue b z := by
  cases b <;> simp [mixedShape,phaseWord,phaseProbe,phaseValue,
    Holant.Marked.SupportAtlas.parity]

theorem shape_odd {K : Type*} [Field K] (b : Bool) (z : K) (x : Word)
    (hx : Holant.weight x % 2 = 1) : mixedShape b z x = 0 := by
  simp [mixedShape,(Holant.Certificates.EqualityQuaternary.parity_weight x).mpr hx]

theorem map_shape {K M : Type*} [Field K] [Field M] (ρ : K →+* M) (b : Bool) (z : K) :
    RingHomRealization.mapSignature ρ (mixedShape b z) = mixedShape b (ρ z) := by
  funext x
  simp only [RingHomRealization.mapSignature,mixedShape]
  split_ifs <;> simp


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankTwo.MixedEndpointBridge
