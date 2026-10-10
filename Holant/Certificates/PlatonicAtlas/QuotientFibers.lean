import Holant.Certificates.PlatonicAtlas.SecantFibers
import Holant.Certificates.PlatonicAtlas.QuotientDirection

/-! The finite secant partition counts actual quotient-direction fibers in the
complex projective quotient, with all arbitrary-representative bridges proved. -/
namespace Holant.Certificates.PlatonicAtlas
open Holant Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
open Holant.Certificates.PlatonicIncidence
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
local instance quotientFibersPointDecidable : DecidableEq Point := Classical.decEq _
local instance quotientFibersSubmoduleDecidable : DecidableEq (Submodule ℂ FourTensor) := Classical.decEq _

 def quotientBuckets (D : Finset Point) (p : Point) : Finset (Finset Point) :=
  (D.erase p).attach.image (fun q => quotientDirectionFiber D p q.val (Finset.mem_erase.mp q.property).1)

 def quotientMultiplicity (D : Finset Point) (p : Point) (n : ℕ) : ℕ :=
  ((quotientBuckets D p).filter (fun B => B.card=n)).card

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

 theorem configuration_fiber_image (K : ι→BinaryMatrix) (hdet : ∀i,(K i).det≠0)
    (hfaith : ∀i j,Proportional (K i) (K j)→i=j)
    (p q : MatchingIndex ι) (hq : q≠p) :
    configurationPoints K hdet (mapFiber (Finset.univ.erase p) (secantMap K p) q)=
      quotientDirectionFiber (configurationPoints K hdet Finset.univ)
        (configurationPoint K hdet p) (configurationPoint K hdet q)
        (fun h => hq (configurationPoint_injective K hdet hfaith h)) := by
  have hi := configurationPoint_injective K hdet hfaith
  have he (r : MatchingIndex ι) (hr : r≠p) :
      quotientDirection (configurationPoint K hdet p) (configurationPoint K hdet q) (fun h => hq (hi h))=
        quotientDirection (configurationPoint K hdet p) (configurationPoint K hdet r) (fun h => hr (hi h)) ↔
      configurationTensor K r∈secantMap K p q :=
    quotientDirection_eq_iff_representative_mem_span _ _ _ _ _
      (configurationTensor K p) (configurationTensor_nonzero K hdet p) rfl
      (configurationTensor K q) (configurationTensor_nonzero K hdet q) rfl
      (configurationTensor K r) (configurationTensor_nonzero K hdet r) rfl
  ext z
  constructor
  · intro hz
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hz
    have hrD := (Finset.mem_filter.mp hr).1
    have hrp := (Finset.mem_erase.mp hrD).1
    have hrS := (secantMap_eq_iff K hdet hfaith p q r hq hrp).mp (Finset.mem_filter.mp hr).2
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_image.mpr ⟨r,Finset.mem_univ _,rfl⟩,
      fun h => hrp (hi h),((he r hrp).mpr hrS).symm⟩
  · intro hz
    obtain ⟨hzD,hrp,hr⟩ := Finset.mem_filter.mp hz
    obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp hzD
    have hrne : r≠p := fun h => hrp (congrArg (configurationPoint K hdet) h)
    apply Finset.mem_image.mpr
    refine ⟨r,Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hrne,Finset.mem_univ _⟩,?_⟩,rfl⟩
    apply (secantMap_eq_iff K hdet hfaith p q r hq hrne).mpr
    exact (he r hrne).mp hr.symm

 theorem configuration_quotientBuckets (K : ι→BinaryMatrix) (hdet : ∀i,(K i).det≠0)
    (hfaith : ∀i j,Proportional (K i) (K j)→i=j) (p : MatchingIndex ι) :
    quotientBuckets (configurationPoints K hdet Finset.univ) (configurationPoint K hdet p)=
      (secantFibers K p).image (configurationPoints K hdet) := by
  ext B
  constructor
  · intro hB
    obtain ⟨⟨q,hq⟩,_,rfl⟩ := Finset.mem_image.mp hB
    have hqD := (Finset.mem_erase.mp hq).2
    obtain ⟨r,_,hr⟩ := Finset.mem_image.mp hqD
    have hrne : r≠p := by
      intro hp
      exact (Finset.mem_erase.mp hq).1 (hr.symm.trans (congrArg (configurationPoint K hdet) hp))
    refine Finset.mem_image.mpr ⟨mapFiber (Finset.univ.erase p) (secantMap K p) r,
      Finset.mem_image.mpr ⟨r,Finset.mem_erase.mpr ⟨hrne,Finset.mem_univ _⟩,rfl⟩,?_⟩
    rw [configuration_fiber_image K hdet hfaith p r hrne]
    subst q
    rfl
  · intro hB
    obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp hB
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hS
    have hqp := (Finset.mem_erase.mp hq).1
    rw [configuration_fiber_image K hdet hfaith p q hqp]
    apply Finset.mem_image.mpr
    refine ⟨⟨configurationPoint K hdet q,Finset.mem_erase.mpr ⟨
      fun h => hqp (configurationPoint_injective K hdet hfaith h),
      Finset.mem_image.mpr ⟨q,Finset.mem_univ _,rfl⟩⟩⟩,Finset.mem_attach _ _,rfl⟩

/-- The source quotient histogram counts actual projective quotient directions,
not candidate secant rows or representative-dependent fingerprints. -/
 theorem quotientMultiplicity_eq_secantFibers (K : ι→BinaryMatrix) (hdet : ∀i,(K i).det≠0)
    (hfaith : ∀i j,Proportional (K i) (K j)→i=j) (p : MatchingIndex ι) (n : ℕ) :
    quotientMultiplicity (configurationPoints K hdet Finset.univ) (configurationPoint K hdet p) n=
      ((secantFibers K p).filter (fun B => B.card=n)).card := by
  unfold quotientMultiplicity
  rw [configuration_quotientBuckets K hdet hfaith]
  have he : ((secantFibers K p).image (configurationPoints K hdet)).filter (fun B => B.card=n)=
      ((secantFibers K p).filter (fun B => B.card=n)).image (configurationPoints K hdet) := by
    ext Q
    simp only [Finset.mem_filter,Finset.mem_image]
    constructor
    · rintro ⟨⟨B,hB,rfl⟩,hc⟩
      exact ⟨B,⟨hB,by simpa only [configurationPoints_card K hdet hfaith] using hc⟩,rfl⟩
    · rintro ⟨B,⟨hB,hc⟩,rfl⟩
      exact ⟨⟨B,hB,rfl⟩,by simpa only [configurationPoints_card K hdet hfaith] using hc⟩
  rw [he,Finset.card_image_of_injective _ (configurationPoints_injective K hdet hfaith)]

end
end Holant.Certificates.PlatonicAtlas
