import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralEightClasses
import Mathlib.Data.List.Permutation

/-! Coefficient extraction from the preserved marked-octahedral proof. Charts are calculated from the OLD canonical pair
and OLD 24 roots. The finite proofs enumerate only fixed four-point lines,
root indices and four-point orders, never arbitrary maps or tensors. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankTwo.HarmonicProjectivities
open Holant.Certificates Holant.Certificates.OctahedralSeparator
open Holant.Certificates.PlatonicIncidence Holant.Certificates.TetrahedralPreservers
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.Preserver
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankTwo.QuotientEnumeration
open scoped Matrix BigOperators

abbrev RawPlane := Fin 2 → Scalar
abbrev RawSmallMatrix := Matrix (Fin 2) (Fin 2) Scalar

/-- The finite arithmetic certificates compare their literal coordinates. -/
instance (priority := 2000) rawPlaneDecEq : DecidableEq RawPlane := fun u v =>
  if h : u 0=v 0 ∧ u 1=v 1 then isTrue (by
    funext i
    fin_cases i
    · exact h.1
    · exact h.2)
  else isFalse (fun he=>h ⟨congrFun he 0,congrFun he 1⟩)

instance (priority := 2000) rawVectorDecEq : DecidableEq RankThree.RawVector := fun u v =>
  if h : u 0=v 0 ∧ u 1=v 1 ∧ u 2=v 2 ∧ u 3=v 3 then isTrue (by
    funext i
    fin_cases i
    · exact h.1
    · exact h.2.1
    · exact h.2.2.1
    · exact h.2.2.2)
  else isFalse (fun he=>h ⟨congrFun he 0,congrFun he 1,congrFun he 2,congrFun he 3⟩)

def rawRoot (k : Fin 4) : RawPlane := fun a => (rootZ k a : Scalar)

def rawCross (u v : RawPlane) : Scalar := u 0*v 1-u 1*v 0

def rawDet (B : RawSmallMatrix) : Scalar := B 0 0*B 1 1-B 0 1*B 1 0

/-- The base row's quaternion dot product gives the actual coefficients
of every marked row, since similarity preserves that bilinear dot product. -/
def lineNorm (t : Fin 122) : Scalar :=
  RankThree.rawDot (rawPoint 0 (canonicalPair t 0)) (rawPoint 0 (canonicalPair t 0))

def lineCoefficients (t : Fin 122) (r : Fin 24) : RawPlane := fun a =>
  RankThree.rawDot (rawPoint 0 (canonicalPair t a)) (rawPoint 0 r)/lineNorm t

def rootScale (v : RawPlane) (k : Fin 4) : Scalar := if k = 1 then v 1 else v 0

/-- First ORIGINAL index on each of the four chart directions. -/
def lineKey (t : Fin 122) (k : Fin 4) : Fin 24 :=
  ((List.finRange 24).find? fun r => decide
    (r ∈ globalLine .octahedral t ∧ rawCross (lineCoefficients t r) (rawRoot k) = 0)).getD (0 : Fin 24)

def lineScale (t : Fin 122) (k : Fin 4) : Scalar :=
  rootScale (lineCoefficients t (lineKey t k)) k

def LineData (t : Fin 122) : Prop :=
  lineNorm t ≠ 0 ∧
  (∀ f : Form,∀ a b : Fin 2,
    RankThree.rawDot (rawPoint f (canonicalPair t a)) (rawPoint f (canonicalPair t b)) =
      if a = b then lineNorm t else 0) ∧
  (∀ f : Form,∀ r : Fin 24,r ∈ globalLine .octahedral t →
    rawPoint f r = lineCoefficients t r 0 • rawPoint f (canonicalPair t 0)+
      lineCoefficients t r 1 • rawPoint f (canonicalPair t 1)) ∧
  (∀ k : Fin 4,lineKey t k ∈ globalLine .octahedral t ∧ lineScale t k ≠ 0 ∧
    lineCoefficients t (lineKey t k) = lineScale t k • rawRoot k) ∧
  (∀ r : Fin 24,r ∈ globalLine .octahedral t → ∃ k : Fin 4,r = lineKey t k)

instance (t : Fin 122) : Decidable (LineData t) := by
  unfold LineData
  infer_instance

/-- Increasing OLD quotient representatives. No proof-dependent order
embedding is evaluated inside the literal arithmetic certificate. -/
def quotientKeys (f : Form) (t : Fin 122) : List (Fin 24) :=
  (List.finRange 24).filter fun r => decide (r ∈ projectedIndices f t)

def quotientValue (f : Form) (t : Fin 122) (i : Fin 4) : RawPlane :=
  projected f t ((quotientKeys f t).getD i.val 0)

def harmonicRaw (v : Fin 4 → RawPlane) : Scalar :=
  rawCross (v 0) (v 2)*rawCross (v 1) (v 3)+
  rawCross (v 0) (v 3)*rawCross (v 1) (v 2)

/-- First of the literal 24 orders satisfying the harmonic identity.
The later certificate proves success and restores all original indices. -/
def quotientOrder (f : Form) (t : Fin 122) : List (Fin 4) :=
  (((List.finRange 4).permutations).find? fun p => decide
    (harmonicRaw (fun i => quotientValue f t (p.getD i.val 0)) = 0)).getD [0,1,2,3]

def quotientKey (f : Form) (t : Fin 122) (k : Fin 4) : Fin 24 :=
  (quotientKeys f t).getD ((quotientOrder f t).getD k.val 0).val 0

def quotientMatrix (f : Form) (t : Fin 122) : RawSmallMatrix :=
  let u := projected f t (quotientKey f t 0)
  let v := projected f t (quotientKey f t 1)
  let w := projected f t (quotientKey f t 2)
  let a := rawCross w v/rawCross u v
  let b := rawCross u w/rawCross u v
  fun i j => if j = 0 then a*u i else b*v i

def quotientCoefficients (f : Form) (t : Fin 122) (r : Fin 24) : RawPlane :=
  let B := quotientMatrix f t
  let v := projected f t r
  ![(B 1 1*v 0-B 0 1*v 1)/rawDet B,
    (B 0 0*v 1-B 1 0*v 0)/rawDet B]

def quotientScale (f : Form) (t : Fin 122) (k : Fin 4) : Scalar :=
  rootScale (quotientCoefficients f t (quotientKey f t k)) k

def QuotientData (f : Form) (t : Fin 122) : Prop :=
  rawDet (quotientMatrix f t) ≠ 0 ∧
  (∀ k : Fin 4,quotientKey f t k ∈ projectedIndices f t ∧
    quotientScale f t k ≠ 0 ∧
    quotientMatrix f t *ᵥ rawRoot k = (quotientScale f t k)⁻¹ •
      projected f t (quotientKey f t k)) ∧
  (∀ r : Fin 24,projected f t r = 0 ∨ ∃ k : Fin 4,
    rootScale (quotientCoefficients f t r) k ≠ 0 ∧
    projected f t r = rootScale (quotientCoefficients f t r) k •
      (quotientMatrix f t *ᵥ rawRoot k))

instance (f : Form) (t : Fin 122) : Decidable (QuotientData f t) := by
  unfold QuotientData
  infer_instance

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankTwo.HarmonicProjectivities
