import Holant.Certificates.PlatonicAtlas.OrbitCertificate
import Holant.Certificates.PlatonicAtlas.Incidences
import Holant.Certificates.RainbowOrbit.Stabilizer

/-! A.19 actual left/right orbits. Every finite word is checked in the original
multiplication dictionary and then interpreted as multiplication of complex matrices. -/
namespace Holant.Certificates.PlatonicAtlas
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
open Holant.Certificates.PlatonicIncidence
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

theorem product_proportional (g : PlatonicModel) (i j : Fin (size g)) :
    Proportional (representative g i*representative g j)
      (representative g (productIndex g i j)) :=
  ⟨(productScale g i j : ℂ),Int.cast_ne_zero.mpr (raw_certificate g i j).1,mul_exact g i j⟩

theorem twoSided_proportional (g : PlatonicModel) (a b k : Fin (size g)) :
    Proportional (representative g a*representative g k*representative g b)
      (representative g (twoSidedIndex g a b k)) :=
  ((product_proportional g a k).mul_right (representative g b)).trans
    (product_proportional g (productIndex g a k) b)

theorem translated_twoSided_proportional (g : PlatonicModel) (i a b k : Fin (size g)) :
    Proportional ((representative g i*representative g a)*representative g k*representative g b)
      (representative g (productIndex g i (twoSidedIndex g a b k))) := by
  have h := ((twoSided_proportional g a b k).mul_left (representative g i)).trans
    (product_proportional g i (twoSidedIndex g a b k))
  simpa only [mul_assoc] using h

theorem globalLine_orbit_image (g : PlatonicModel) (t : Fin (secantCount g)) :
    globalLine g t=(baseLine g (seed g (globalLine g t).card)).image
      (fun k => productIndex g (globalWitness g t).1
        (twoSidedIndex g (baseWord g (globalWitness g t).2).1
          (baseWord g (globalWitness g t).2).2 k)) := by
  have hc : (globalLine g t).card=(baseLine g (globalWitness g t).2).card := by
    rw [globalLine_eq_translated,translatedLine_card]
  rw [hc,globalLine_eq_translated]
  unfold translatedLine
  have h := base_orbit_certificate g (globalWitness g t).2
  change (baseLine g (seed g (baseLine g (globalWitness g t).2).card)).image
    (twoSidedIndex g (baseWord g (globalWitness g t).2).1
      (baseWord g (globalWitness g t).2).2)=baseLine g (globalWitness g t).2 at h
  calc
    (baseLine g (globalWitness g t).2).image (productIndex g (globalWitness g t).1) =
        ((baseLine g (seed g (baseLine g (globalWitness g t).2).card)).image
          (twoSidedIndex g (baseWord g (globalWitness g t).2).1
            (baseWord g (globalWitness g t).2).2)).image
          (productIndex g (globalWitness g t).1) := congrArg _ h.symm
    _ = _ := by rw [Finset.image_image]; rfl

theorem baseLine_actual (g : PlatonicModel) (b : Fin (baseCount g)) :
    DomainSecant g (baseLine g b) := by
  refine ⟨identityIndex g,baseAnchor g b,Ne.symm (base_anchors g b).1,?_⟩
  intro k
  rw [representative_identity]
  exact baseLine_iff g b k

/-- Every complete actual domain secant is in the actual left/right group orbit
of the fixed source secant of its size. All original representative labels and
projective scalar equalities are retained. In particular this covers each of
A.19's displayed rich families. -/
theorem actual_left_right_orbit (g : PlatonicModel) (S : Finset (Fin (size g)))
    (hS : DomainSecant g S) :
    ∃U V : Mat,groupDirection g U ∧ groupDirection g V ∧
      ∀k : Fin (size g),k∈S ↔ ∃j∈baseLine g (seed g S.card),
        Proportional (representative g k) (U*representative g j*V) := by
  classical
  obtain ⟨t,_,rfl⟩ := Finset.mem_map.mp ((domainLines_exact g S).mpr hS)
  let i := (globalWitness g t).1
  let a := (baseWord g (globalWitness g t).2).1
  let b := (baseWord g (globalWitness g t).2).2
  refine ⟨representative g i*representative g a,representative g b,
    groupDirection_mul g (representative_mem g i) (representative_mem g a),
    representative_mem g b,?_⟩
  intro k
  change k∈globalLine g t ↔ _
  rw [globalLine_orbit_image]
  constructor
  · intro hk
    obtain ⟨j,hj,hk⟩ := Finset.mem_image.mp hk
    refine ⟨j,hj,?_⟩
    have hp := translated_twoSided_proportional g i a b j
    rw [show productIndex g i (twoSidedIndex g a b j)=k from hk] at hp
    exact hp.symm
  · rintro ⟨j,hj,hp⟩
    have hh := hp.trans (translated_twoSided_proportional g i a b j)
    obtain ⟨c,_,hc⟩ := hh
    have hk := projectively_injective g k (productIndex g i (twoSidedIndex g a b j)) c hc
    exact Finset.mem_image.mpr ⟨j,hj,hk.symm⟩

end
end Holant.Certificates.PlatonicAtlas
