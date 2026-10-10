import Holant.Certificates.PlatonicAtlas.FiberPartition
import Holant.Certificates.PlatonicIncidence.MonochromaticMaximal

/-! Quotient buckets as complete actual complex secants with their base
point removed. The finite source indices remain projectively faithful. -/
namespace Holant.Certificates.PlatonicAtlas
open Holant Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
open Holant.Certificates.PlatonicIncidence
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
local instance secantFibersPointDecidable : DecidableEq Point := Classical.decEq _

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

 def secantMap (K : ι→BinaryMatrix) (p q : MatchingIndex ι) : Submodule ℂ FourTensor :=
  Submodule.span ℂ ({configurationTensor K p,configurationTensor K q} : Set FourTensor)

 local instance secantFibersSubmoduleDecidable : DecidableEq (Submodule ℂ FourTensor) := Classical.decEq _

 def secantFibers (K : ι→BinaryMatrix) (p : MatchingIndex ι) : Finset (Finset (MatchingIndex ι)) :=
  fiberFamily (Finset.univ.erase p) (secantMap K p)

 theorem secantMap_self_mem (K : ι→BinaryMatrix) (p q : MatchingIndex ι) :
    configurationTensor K p∈secantMap K p q := Submodule.subset_span (by simp [secantMap])

 theorem secantMap_other_mem (K : ι→BinaryMatrix) (p q : MatchingIndex ι) :
    configurationTensor K q∈secantMap K p q := Submodule.subset_span (by simp [secantMap])

 theorem secantMap_eq_iff (K : ι→BinaryMatrix) (hdet : ∀i,(K i).det≠0)
    (hfaith : ∀i j,Proportional (K i) (K j)→i=j)
    (p q r : MatchingIndex ι) (hq : q≠p) (hr : r≠p) :
    secantMap K p r=secantMap K p q ↔ configurationTensor K r∈secantMap K p q := by
  constructor
  · intro h
    rw [←h]
    exact secantMap_other_mem K p r
  · intro h
    exact (configuration_subspace_eq_pair K hdet hfaith (secantMap K p q)
      (by rw [secantMap,configuration_pair_finrank K hdet hfaith p q (Ne.symm hq)])
      p r (Ne.symm hr) (secantMap_self_mem K p q) h).symm

 theorem secant_fiber_exact (K : ι→BinaryMatrix) (hdet : ∀i,(K i).det≠0)
    (hfaith : ∀i j,Proportional (K i) (K j)→i=j)
    (p q : MatchingIndex ι) (hq : q≠p) :
    mapFiber (Finset.univ.erase p) (secantMap K p) q=
      (configurationIntersection K (secantMap K p q)).erase p := by
  ext r
  simp only [mapFiber,Finset.mem_filter,Finset.mem_erase,Finset.mem_univ,and_true,
    mem_configurationIntersection]
  exact and_congr_right (fun hr => secantMap_eq_iff K hdet hfaith p q r hq hr)

 theorem secantFiber_omit_base (K : ι→BinaryMatrix) (p : MatchingIndex ι)
    (B : Finset (MatchingIndex ι)) (hB : B∈secantFibers K p) : p∉B := by
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hB
  simp [mapFiber]

 theorem insert_secantFiber (K : ι→BinaryMatrix) (hdet : ∀i,(K i).det≠0)
    (hfaith : ∀i j,Proportional (K i) (K j)→i=j)
    (p : MatchingIndex ι) (B : Finset (MatchingIndex ι)) (hB : B∈secantFibers K p) :
    MatchingSecant K (insert p B) := by
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hB
  have hqp := (Finset.mem_erase.mp hq).1
  rw [secant_fiber_exact K hdet hfaith p q hqp,
    Finset.insert_erase (by exact (mem_configurationIntersection _ _ _).mpr (secantMap_self_mem K p q))]
  exact ⟨p,q,Ne.symm hqp,fun x => mem_configurationIntersection K (secantMap K p q) x⟩

 theorem matchingSecant_erase_mem (K : ι→BinaryMatrix) (hdet : ∀i,(K i).det≠0)
    (hfaith : ∀i j,Proportional (K i) (K j)→i=j)
    (p : MatchingIndex ι) (S : Finset (MatchingIndex ι))
    (hS : MatchingSecant K S) (hp : p∈S) (hc : 2≤S.card) :
    S.erase p∈secantFibers K p := by
  obtain ⟨q,hq⟩ : (S.erase p).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_erase_of_mem hp]
    omega
  have hqp := (Finset.mem_erase.mp hq).1
  have hs := matchingSecant_rebase K hdet hfaith S hS p q hp (Finset.mem_erase.mp hq).2 (Ne.symm hqp)
  have he : S=configurationIntersection K (secantMap K p q) := by
    ext x
    exact (hs x).trans (mem_configurationIntersection _ _ _).symm
  apply Finset.mem_image.mpr
  refine ⟨q,Finset.mem_erase.mpr ⟨hqp,Finset.mem_univ _⟩,?_⟩
  rw [secant_fiber_exact K hdet hfaith p q hqp,he]

 theorem secantFiber_card_add_one (K : ι→BinaryMatrix) (p : MatchingIndex ι)
    (B : Finset (MatchingIndex ι)) (hB : B∈secantFibers K p) :
    (insert p B).card=B.card+1 := Finset.card_insert_of_notMem (secantFiber_omit_base K p B hB)

 theorem actual_rich_fiber_count (K : ι→BinaryMatrix) (hdet : ∀i,(K i).det≠0)
    (hfaith : ∀i j,Proportional (K i) (K j)→i=j)
    (p : MatchingIndex ι) (n : ℕ) (hn : 2≤n) :
    {Q : Finset Point | ActualRichLine K hdet Q ∧ configurationPoint K hdet p∈Q ∧
      Q.card=n+1}.ncard=((secantFibers K p).filter (fun B => B.card=n)).card := by
  let F := fun B : Finset (MatchingIndex ι) => configurationPoints K hdet (insert p B)
  have he : {Q : Finset Point | ActualRichLine K hdet Q ∧ configurationPoint K hdet p∈Q ∧ Q.card=n+1}=
      (((secantFibers K p).filter (fun B => B.card=n)).image F : Set _) := by
    ext Q
    simp only [Set.mem_setOf_eq,Finset.mem_coe,Finset.mem_image,Finset.mem_filter]
    constructor
    · rintro ⟨hQ,hp,hcard⟩
      obtain ⟨S,hS,hc,rfl⟩ := (actualRichLine_iff K hdet hfaith Q).mp hQ
      have hpS : p∈S := by
        obtain ⟨q,hq,heq⟩ := Finset.mem_image.mp hp
        exact (configurationPoint_injective K hdet hfaith heq) ▸ hq
      refine ⟨S.erase p,⟨matchingSecant_erase_mem K hdet hfaith p S hS hpS (by omega),?_⟩,?_⟩
      · rw [configurationPoints_card K hdet hfaith] at hcard
        rw [Finset.card_erase_of_mem hpS]
        omega
      · dsimp [F]
        rw [Finset.insert_erase hpS]
    · rintro ⟨B,⟨hB,hc⟩,rfl⟩
      refine ⟨(actualRichLine_iff K hdet hfaith _).mpr
        ⟨insert p B,insert_secantFiber K hdet hfaith p B hB,?_,rfl⟩,?_,?_⟩
      · rw [secantFiber_card_add_one K p B hB,hc]
        omega
      · exact Finset.mem_image.mpr ⟨p,Finset.mem_insert_self _ _,rfl⟩
      · rw [configurationPoints_card K hdet hfaith,secantFiber_card_add_one K p B hB,hc]
  rw [he,Set.ncard_coe_finset]
  apply Finset.card_image_iff.mpr
  intro B hB C hC hBC
  have hi := configurationPoints_injective K hdet hfaith hBC
  have hb := secantFiber_omit_base K p B (Finset.mem_filter.mp hB).1
  have hc := secantFiber_omit_base K p C (Finset.mem_filter.mp hC).1
  have hh := congrArg (fun S : Finset (MatchingIndex ι) => S.erase p) hi
  simpa [Finset.erase_insert,hb,hc] using hh

end
end Holant.Certificates.PlatonicAtlas
