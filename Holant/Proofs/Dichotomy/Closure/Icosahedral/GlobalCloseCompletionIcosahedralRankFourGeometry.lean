import Holant.Proofs.Dichotomy.Closure.Icosahedral.GlobalCloseCompletionIcosahedralPreserver
import Holant.Certificates.PlatonicIncidence.CoefficientEquivs
import Holant.Certificates.PlatonicIncidence.DomainLines
import Holant.Certificates.MatchingProductBridge.GroupInverses

/-! Generic I/opposite-I coefficient proof extracted from RankFour/Geometry.
No old saved-State dispatcher or caller-supplied classification is imported.
This candidate retains the actual full sixty-point hypotheses and proof. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 32768

noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIcosahedral.RankFour
open Holant Holant.Certificates Holant.Certificates.MatchingProductBridge
open Holant.Certificates.RainbowOrbit Holant.Certificates.PlatonicIncidence
open Holant.Certificates.TetrahedralPreservers
open Preserver.Completion
open scoped BigOperators Matrix

def polar (u v : V) : ℂ := ∑ i : Fin 4, u i * v i

theorem polar_smul (a b : ℂ) (u v : V) :
    polar (a • u) (b • v) = (a*b) * polar u v := by
  simp only [polar,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem polar_smul_right (a : ℂ) (u v : V) : polar u (a • v) = a * polar u v := by
  simp only [polar,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem polar_add_self (u v : V) :
    polar (u+v) (u+v) = polar u u + 2*polar u v + polar v v := by
  simp only [polar,Fin.sum_univ_four,Pi.add_apply]
  ring

private theorem scalar_determinant_polar (a b c d : ℂ) :
    a*d-b*c = polar
      (![ (a+d)/2, -(Complex.I/2)*(b+c), (b-c)/2, -(Complex.I/2)*(a-d)] : V)
      (![ (a+d)/2, -(Complex.I/2)*(b+c), (b-c)/2, -(Complex.I/2)*(a-d)] : V) := by
  simp only [polar,Fin.sum_univ_four]
  change a*d-b*c =
    ((a+d)/2)*((a+d)/2) + (-(Complex.I/2)*(b+c))*(-(Complex.I/2)*(b+c)) +
    ((b-c)/2)*((b-c)/2) + (-(Complex.I/2)*(a-d))*(-(Complex.I/2)*(a-d))
  ring_nf <;> simp only [Complex.I_sq] <;> ring

theorem determinant_polar (U : Matrix Bool Bool ℂ) : U.det = polar (coordinates U) (coordinates U) := by
  let a : ℂ := U false false
  let b : ℂ := U false true
  let c : ℂ := U true false
  let d : ℂ := U true true
  have hdet : binaryDeterminant U = a*d-b*c := rfl
  have hcoordinates : coordinates U =
      (![ (a+d)/2, -(Complex.I/2)*(b+c), (b-c)/2, -(Complex.I/2)*(a-d)] : V) := rfl
  calc
    U.det = binaryDeterminant U := (binaryDeterminant_eq_det U).symm
    _ = a*d-b*c := hdet
    _ = _ := scalar_determinant_polar a b c d
    _ = polar (coordinates U) (coordinates U) :=
      congrArg₂ polar hcoordinates.symm hcoordinates.symm

def binaryPolar (U W : Matrix Bool Bool ℂ) : ℂ := ((U+W).det-U.det-W.det)/2

theorem coordinates_polar (U W : Matrix Bool Bool ℂ) :
    polar (coordinates U) (coordinates W) = binaryPolar U W := by
  simp only [binaryPolar,determinant_polar,map_add,
    polar_add_self]
  ring

theorem polar_left (P U W : Matrix Bool Bool ℂ) :
    polar (coordinates (P*U)) (coordinates (P*W)) =
      P.det * polar (coordinates U) (coordinates W) := by
  simp only [coordinates_polar,binaryPolar,←Matrix.mul_add,Matrix.det_mul]
  ring

theorem polar_one (U : Matrix Bool Bool ℂ) : polar (coordinates 1) (coordinates U) = coordinates U 0 := by
  simp only [polar,Fin.sum_univ_four,coordinates_one]
  norm_num

def standardPoint (i : Fin 60) : V := coordinates (representative .icosahedral i)

/-- Exact analytic map from the old I coefficients to the current literal
I/opposite-I kernel coefficients. No gadget is installed. -/
def frame (opposite : Bool) : V ≃ₗ[ℂ] V := by
  cases opposite
  · exact LinearEquiv.refl ℂ V
  · exact (coordinates.symm.trans kappaEquiv).trans coordinates

theorem point_frame (opposite : Bool) (i : Fin 60) :
    point opposite i = frame opposite (standardPoint i) := by
  cases opposite
  · rfl
  · change coordinates (OppositeIcosahedral.kappa (representative .icosahedral i)) =
      coordinates (OppositeIcosahedral.kappa (coordinates.symm
        (coordinates (representative .icosahedral i))))
    rw [coordinates.symm_apply_apply]

def rowPolar (opposite : Bool) (u v : V) : ℂ :=
  polar ((frame opposite).symm u) ((frame opposite).symm v)

theorem rowPolar_point (opposite : Bool) (i j : Fin 60) :
    rowPolar opposite (point opposite i) (point opposite j) =
      polar (standardPoint i) (standardPoint j) := by
  simp only [point_frame,rowPolar,LinearEquiv.symm_apply_apply]

theorem rowPolar_smul (opposite : Bool) (a b : ℂ) (u v : V) :
    rowPolar opposite (a • u) (b • v) = (a*b)*rowPolar opposite u v := by
  simp only [rowPolar,map_smul,polar_smul]

def secant (opposite : Bool) (i j : Fin 60) : Finset (Fin 60) := by
  classical
  exact Finset.univ.filter fun k =>
    point opposite k ∈ Submodule.span ℂ ({point opposite i,point opposite j} : Set V)

@[simp] theorem mem_secant (opposite : Bool) (i j k : Fin 60) :
    k ∈ secant opposite i j ↔
      point opposite k ∈ Submodule.span ℂ ({point opposite i,point opposite j} : Set V) := by
  classical
  simp only [secant,Finset.mem_filter,Finset.mem_univ,true_and]

def standardSecant (i j : Fin 60) : Finset (Fin 60) := by
  classical
  exact Finset.univ.filter fun k => representative .icosahedral k ∈
    Submodule.span ℂ ({representative .icosahedral i,representative .icosahedral j} : Set Mat)

@[simp] theorem mem_standardSecant (i j k : Fin 60) :
    k ∈ standardSecant i j ↔ representative .icosahedral k ∈
      Submodule.span ℂ ({representative .icosahedral i,representative .icosahedral j} : Set Mat) := by
  classical
  simp only [standardSecant,Finset.mem_filter,Finset.mem_univ,true_and]

theorem secant_standard (opposite : Bool) (i j : Fin 60) :
    secant opposite i j = standardSecant i j := by
  ext k
  simp only [mem_secant,mem_standardSecant,point_frame]
  rw [equiv_span_pair (frame opposite)]
  exact equiv_span_pair coordinates _ _ _

/-- Small exact integer profile, not a permutation enumeration.  It says
that the complete identity line has two points exactly for a pure
imaginary quaternion row. The identity row itself is explicitly excluded. -/
def IdentityProfile (j : Fin 60) : Prop := j=0 ∨
  ((icosahedralLines (icosahedralLineOf j)).card=2 ↔ icosahedralRaw j 0=GoldenInt.zero)

instance (j : Fin 60) : Decidable (IdentityProfile j) := by
  unfold IdentityProfile
  infer_instance

theorem identity_profile (j : Fin 60) : IdentityProfile j := by
  fin_cases j <;> decide +kernel

/-- Every arbitrary pair uses the OLD complete identity secant and its
actual left multiplication permutation; no secant classification is a
caller premise. -/
theorem pair_transport (i j : Fin 60) (hij : i ≠ j) :
    ∃ a : Fin 60, a ≠ 0 ∧
      j = productIndex .icosahedral i a ∧
      (standardSecant i j).card = (icosahedralLines (icosahedralLineOf a)).card ∧
      (polar (standardPoint i) (standardPoint j)=0 ↔ icosahedralRaw a 0=GoldenInt.zero) := by
  classical
  let p : Equiv.Perm (Fin 60) := leftPermutation .icosahedral i
  obtain ⟨a,ha⟩ := p.surjective j
  have hproduct : productIndex .icosahedral i a = j :=
    (leftPermutation_apply .icosahedral i a).symm.trans ha
  have hane : a ≠ 0 := by
    intro he
    subst a
    have hi0 : productIndex .icosahedral i (0 : Fin 60) = i :=
      product_identity_right .icosahedral i
    have hj : j=i := hproduct.symm.trans hi0
    exact hij hj.symm
  have hset : standardSecant i j =
      translatedLine .icosahedral i (baseLineOf .icosahedral a) := by
    ext k
    obtain ⟨l,hl⟩ := p.surjective k
    have hk : productIndex .icosahedral i l = k :=
      (leftPermutation_apply .icosahedral i l).symm.trans hl
    have hbaseEq : (l ∈ baseSecant .icosahedral a) =
        (l ∈ baseLine .icosahedral (baseLineOf .icosahedral a)) :=
      congrArg (fun S : Finset (Fin 60) => l ∈ S) (base_certificate .icosahedral a hane)
    have hbase : l ∈ baseSecant .icosahedral a ↔
        l ∈ baseLine .icosahedral (baseLineOf .icosahedral a) :=
      ⟨hbaseEq.mp,hbaseEq.mpr⟩
    have hpair : productIndex .icosahedral i l ∈
        standardSecant i (productIndex .icosahedral i a) ↔
        productIndex .icosahedral i l ∈
          translatedLine .icosahedral i (baseLineOf .icosahedral a) :=
      (mem_standardSecant i (productIndex .icosahedral i a)
        (productIndex .icosahedral i l)).trans
        ((product_span_iff .icosahedral i a l).trans
          ((baseSecant_iff .icosahedral a l hane).symm.trans
            (hbase.trans
              (mem_translated_product .icosahedral i l (baseLineOf .icosahedral a)).symm)))
    have hleft : (productIndex .icosahedral i l ∈
        standardSecant i (productIndex .icosahedral i a)) = (k ∈ standardSecant i j) :=
      congrArg₂ (fun x y : Fin 60 => x ∈ standardSecant i y) hk hproduct
    have hright : (productIndex .icosahedral i l ∈
        translatedLine .icosahedral i (baseLineOf .icosahedral a)) =
        (k ∈ translatedLine .icosahedral i (baseLineOf .icosahedral a)) :=
      congrArg (fun x : Fin 60 =>
        x ∈ translatedLine .icosahedral i (baseLineOf .icosahedral a)) hk
    exact ⟨fun hx => hright.mp (hpair.mp (hleft.mpr hx)),
      fun hx => hleft.mp (hpair.mpr (hright.mpr hx))⟩
  have hcard : (standardSecant i j).card =
      (icosahedralLines (icosahedralLineOf a)).card := by
    calc
      (standardSecant i j).card =
          ((baseLine .icosahedral (baseLineOf .icosahedral a)).image
            (productIndex .icosahedral i)).card := congrArg Finset.card hset
      _ = (baseLine .icosahedral (baseLineOf .icosahedral a)).card :=
        Finset.card_image_of_injective _ (left_product_injective .icosahedral i)
      _ = (icosahedralLines (icosahedralLineOf a)).card := rfl
  have hc : (productScale .icosahedral i a : ℂ) ≠ 0 :=
    Int.cast_ne_zero.mpr (raw_certificate .icosahedral i a).1
  have hd := representative_det_ne_zero .icosahedral i
  have ht0 := polar_left (representative .icosahedral i) (1 : Matrix Bool Bool ℂ)
    (representative .icosahedral a)
  have ht : polar (coordinates (representative .icosahedral i))
      (coordinates (representative .icosahedral i * representative .icosahedral a)) =
      (representative .icosahedral i).det * coordinates (representative .icosahedral a) 0 := by
    simpa only [Matrix.mul_one,polar_one] using ht0
  have hcoordinates : coordinates
      (representative .icosahedral i * representative .icosahedral a) =
      (productScale .icosahedral i a : ℂ) • standardPoint j := by
    calc
      _ = coordinates ((productScale .icosahedral i a : ℂ) •
          representative .icosahedral (productIndex .icosahedral i a)) :=
        congrArg coordinates (mul_exact .icosahedral i a)
      _ = (productScale .icosahedral i a : ℂ) •
          coordinates (representative .icosahedral (productIndex .icosahedral i a)) :=
        coordinates.map_smul _ _
      _ = _ := congrArg (fun x : Fin 60 =>
        (productScale .icosahedral i a : ℂ) • standardPoint x) hproduct
  have hpolar : polar (coordinates (representative .icosahedral i))
      (coordinates (representative .icosahedral i * representative .icosahedral a)) =
      (productScale .icosahedral i a : ℂ) * polar (standardPoint i) (standardPoint j) :=
    (congrArg (polar (standardPoint i)) hcoordinates).trans
      (polar_smul_right (productScale .icosahedral i a : ℂ) (standardPoint i) (standardPoint j))
  have ht' : (productScale .icosahedral i a : ℂ) *
      polar (standardPoint i) (standardPoint j) =
      (representative .icosahedral i).det * coordinates (representative .icosahedral a) 0 :=
    hpolar.symm.trans ht
  have hzero : polar (standardPoint i) (standardPoint j)=0 ↔
      coordinates (representative .icosahedral a) 0=0 := by
    constructor
    · intro hz
      have he : (representative .icosahedral i).det *
          coordinates (representative .icosahedral a) 0 = 0 :=
        ht'.symm.trans
          ((congrArg (fun z : ℂ => (productScale .icosahedral i a : ℂ) * z) hz).trans
            (mul_zero _))
      exact (mul_eq_zero.mp he).resolve_left hd
    · intro hz
      have he : (productScale .icosahedral i a : ℂ) *
          polar (standardPoint i) (standardPoint j) = 0 :=
        ht'.trans
          ((congrArg (fun z : ℂ => (representative .icosahedral i).det * z) hz).trans
            (mul_zero _))
      exact (mul_eq_zero.mp he).resolve_left hc
  refine ⟨a,hane,hproduct.symm,hcard,hzero.trans ?_⟩
  change coordinates (goldenMatrix (icosahedralRaw a)) 0=0 ↔ _
  rw [coordinates_golden]
  exact complex_golden_zero_iff _

/-- H4-only geometric producer: two-point secants are exactly orthogonal
root pairs in the literal determinant coefficient chart. -/
theorem secant_two_iff_orthogonal (opposite : Bool) (i j : Fin 60) (hij : i ≠ j) :
    (secant opposite i j).card=2 ↔ rowPolar opposite (point opposite i) (point opposite j)=0 := by
  obtain ⟨a,ha,hj,hcard,hpolar⟩ := pair_transport i j hij
  have hp : (icosahedralLines (icosahedralLineOf a)).card=2 ↔
      icosahedralRaw a 0=GoldenInt.zero := (identity_profile a).resolve_left ha
  rw [secant_standard,hcard,rowPolar_point]
  exact hp.trans hpolar.symm

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIcosahedral.RankFour
end
