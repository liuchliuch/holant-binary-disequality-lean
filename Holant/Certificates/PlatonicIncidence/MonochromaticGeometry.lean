import Holant.Certificates.PlatonicIncidence.MonochromaticRuling
import Holant.Certificates.PlatonicIncidence.MonochromaticCounting

/-! Complete complex matching-deck span intersections and Segre rulings for any
finite family of invertible, projectively distinct binary representatives. -/
namespace Holant.Certificates.PlatonicIncidence
open Holant Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def configurationTensor (K : ι → BinaryMatrix) (p : MatchingIndex ι) : FourTensor :=
  matchingTensor p.1 (K p.2.1) (K p.2.2)

def BinarySecant (K : ι → BinaryMatrix) (L : Finset ι) : Prop :=
  ∃ i j, i≠j ∧ ∀ k, k∈L ↔ K k∈Submodule.span ℂ ({K i,K j} : Set BinaryMatrix)

/-- The complete deck intersection of the actual complex line spanned by two
distinct labeled matching products. -/
def MatchingSecant (K : ι → BinaryMatrix) (S : Finset (MatchingIndex ι)) : Prop :=
  ∃ p q, p≠q ∧ ∀ x, x∈S ↔ configurationTensor K x∈Submodule.span ℂ
    ({configurationTensor K p,configurationTensor K q} : Set FourTensor)

def HasOneMatching (S : Finset (MatchingIndex ι)) : Prop :=
  ∃ r : Fin 3, ∀ p∈S,p.1=r

theorem configurationTensor_nonzero (K : ι → BinaryMatrix)
    (hdet : ∀i,(K i).det≠0) (p : MatchingIndex ι) : configurationTensor K p≠0 :=
  matching_nonzero p.1 _ _ (hdet _) (hdet _)

theorem configurationTensor_proportional_iff (K : ι → BinaryMatrix)
    (hdet : ∀i,(K i).det≠0)
    (hfaith : ∀ i j,Proportional (K i) (K j)→i=j) (p q : MatchingIndex ι) :
    Proportional (configurationTensor K p) (configurationTensor K q) ↔ p=q := by
  constructor
  · rcases p with ⟨r,i,j⟩
    rcases q with ⟨s,k,l⟩
    intro hp
    have hrs := proportional_matching_labels r s (K i) (K j) (K k) (K l)
      (hdet i) (hdet j) (hdet k) (hdet l) hp
    subst s
    obtain ⟨hik,hjl⟩ := proportional_matching_factors r (K i) (K j) (K k) (K l)
      (hdet i) (hdet j) hp
    rw [hfaith i k hik,hfaith j l hjl]
  · rintro rfl
    exact Proportional.refl _

theorem MatchingSecant.endpoints_mem (K : ι → BinaryMatrix)
    (S : Finset (MatchingIndex ι)) (p q : MatchingIndex ι)
    (hS : ∀x,x∈S ↔ configurationTensor K x∈Submodule.span ℂ
      ({configurationTensor K p,configurationTensor K q} : Set FourTensor)) : p∈S ∧ q∈S := by
  constructor
  · exact (hS p).mpr (Submodule.subset_span (by simp))
  · exact (hS q).mpr (Submodule.subset_span (by simp))

/-- Every one-factor ruling over a domain secant is already maximal in the
whole matching deck, including all three matching labels. -/
theorem rulingSet_matchingSecant (K : ι → BinaryMatrix)
    (hdet : ∀i,(K i).det≠0)
    (hfaith : ∀ i j,Proportional (K i) (K j)→i=j)
    (r : Fin 3) (b : Bool) (f : ι) (L : Finset ι) (hL : BinarySecant K L) :
    MatchingSecant K (rulingSet r b f L) := by
  obtain ⟨i,j,hij,hL⟩ := hL
  have hprop (k l : ι) : Proportional (K k) (K l) ↔ k=l :=
    ⟨hfaith k l,by rintro rfl; exact Proportional.refl _⟩
  cases b
  · refine ⟨(r,f,i),(r,f,j),?_,?_⟩
    · intro h
      exact hij (congrArg (fun p => p.2.2) h)
    · rintro ⟨s,k,l⟩
      simp only [mem_rulingSet,Bool.false_eq_true,↓reduceIte]
      change (s=r ∧ k=f ∧ l∈L) ↔ _
      rw [hL l]
      exact (matching_mem_right_span_iff r s (K f) (K i) (K j) (K k) (K l)
        (hdet f) (hdet i) (hdet j) (hdet k) (hdet l)).trans
        (by rw [hprop k f]) |>.symm
  · refine ⟨(r,i,f),(r,j,f),?_,?_⟩
    · intro h
      exact hij (congrArg (fun p => p.2.1) h)
    · rintro ⟨s,k,l⟩
      simp only [mem_rulingSet,↓reduceIte]
      change (s=r ∧ l=f ∧ k∈L) ↔ _
      rw [hL k]
      exact (matching_mem_left_span_iff r s (K i) (K j) (K f) (K k) (K l)
        (hdet i) (hdet j) (hdet f) (hdet k) (hdet l)).trans
        (by rw [hprop l f]) |>.symm

/-- Canonical finite intersection with an actual two-point domain span. -/
def binarySecantSet (K : ι → BinaryMatrix) (i j : ι) : Finset ι := by
  classical
  exact Finset.univ.filter (fun k => K k∈Submodule.span ℂ ({K i,K j} : Set BinaryMatrix))

@[simp] theorem mem_binarySecantSet (K : ι → BinaryMatrix) (i j k : ι) :
    k∈binarySecantSet K i j ↔ K k∈Submodule.span ℂ ({K i,K j} : Set BinaryMatrix) := by
  classical
  simp [binarySecantSet]

theorem binarySecantSet_exact (K : ι → BinaryMatrix) (i j : ι) (hij : i≠j) :
    BinarySecant K (binarySecantSet K i j) := ⟨i,j,hij,mem_binarySecantSet K i j⟩

/-- Every rich monochromatic actual complex secant has exactly one varying
ordered factor. The factor decomposition is a conclusion of the minor proof. -/
theorem monochromatic_secant_ruling (K : ι → BinaryMatrix)
    (hdet : ∀i,(K i).det≠0)
    (hfaith : ∀ i j,Proportional (K i) (K j)→i=j)
    (S : Finset (MatchingIndex ι)) (hS : MatchingSecant K S) (hrich : 3≤S.card)
    (hone : HasOneMatching S) :
    ∃ r b f L, BinarySecant K L ∧ 3≤L.card ∧ S=rulingSet r b f L := by
  classical
  obtain ⟨⟨r,i,j⟩,⟨s,k,l⟩,hne,hspan⟩ := hS
  obtain ⟨hp,hq⟩ := MatchingSecant.endpoints_mem K S (r,i,j) (s,k,l) hspan
  obtain ⟨t,ht⟩ := hone
  have hrs : r=s := (ht _ hp).trans (ht _ hq).symm
  subst s
  have hex : ∃ w∈S,w≠(r,i,j) ∧ w≠(r,k,l) := by
    by_contra hn
    push_neg at hn
    have hsub : S⊆{(r,i,j),(r,k,l)} := by
      intro w hw
      by_cases hwp : w=(r,i,j)
      · simp [hwp]
      · simp [hn w hw hwp]
    have hc := Finset.card_le_card hsub
    have hc' : ({(r,i,j),(r,k,l)} : Finset (MatchingIndex ι)).card≤2 := Finset.card_le_two
    omega
  obtain ⟨⟨u,m,n⟩,hw,hwp,hwq⟩ := hex
  have hur : u=r := (ht _ hw).trans (ht _ hp).symm
  subst u
  obtain ⟨a,b,he⟩ := Submodule.mem_span_pair.mp ((hspan _).mp hw)
  have hcoeff : a≠0 ∧ b≠0 := by
    constructor
    · intro ha
      have hb : b≠0 := by
        intro hb
        exact configurationTensor_nonzero K hdet (r,m,n) (by simpa [ha,hb] using he.symm)
      apply hwq
      exact (configurationTensor_proportional_iff K hdet hfaith _ _).mp
        ⟨b,hb,by simpa [ha] using he.symm⟩
    · intro hb
      have ha : a≠0 := by
        intro ha
        exact configurationTensor_nonzero K hdet (r,m,n) (by simpa [ha,hb] using he.symm)
      apply hwp
      exact (configurationTensor_proportional_iff K hdet hfaith _ _).mp
        ⟨a,ha,by simpa [hb] using he.symm⟩
  have hrule := matching_sum_ruling r (K i) (K j) (K k) (K l) (K m) (K n)
    (hdet i) (hdet j) (hdet k) (hdet l) a b hcoeff.1 hcoeff.2 he.symm
  rcases hrule with hik | hjl
  · have hik' := hfaith i k hik
    subst k
    have hjl : j≠l := by intro h; subst l; exact hne rfl
    let L := binarySecantSet K j l
    have hL : BinarySecant K L := binarySecantSet_exact K j l hjl
    have heq : S=rulingSet r false i L := by
      ext ⟨s,x,y⟩
      rw [hspan]
      simp only [configurationTensor]
      rw [matching_mem_right_span_iff r s _ _ _ _ _ (hdet i) (hdet j) (hdet l) (hdet x) (hdet y)]
      simp only [mem_rulingSet,Bool.false_eq_true,↓reduceIte,mem_binarySecantSet,L]
      exact and_congr_right (fun _ => and_congr
        ⟨hfaith x i,by rintro rfl; exact Proportional.refl _⟩ Iff.rfl)
    refine ⟨r,false,i,L,hL,?_,heq⟩
    simpa [heq] using hrich
  · have hjl' := hfaith j l hjl
    subst l
    have hik : i≠k := by intro h; subst k; exact hne rfl
    let L := binarySecantSet K i k
    have hL : BinarySecant K L := binarySecantSet_exact K i k hik
    have heq : S=rulingSet r true j L := by
      ext ⟨s,x,y⟩
      rw [hspan]
      simp only [configurationTensor]
      rw [matching_mem_left_span_iff r s _ _ _ _ _ (hdet i) (hdet k) (hdet j) (hdet x) (hdet y)]
      simp only [mem_rulingSet,↓reduceIte,mem_binarySecantSet,L]
      exact and_congr_right (fun _ => and_congr
        ⟨hfaith y j,by rintro rfl; exact Proportional.refl _⟩ Iff.rfl)
    refine ⟨r,true,j,L,hL,?_,heq⟩
    simpa [heq] using hrich

/-- The combinatorial ruling family is exactly the complete rich
monochromatic intersections with actual complex projective lines. -/
theorem monochromaticLines_exact (K : ι → BinaryMatrix)
    (hdet : ∀i,(K i).det≠0)
    (hfaith : ∀ i j,Proportional (K i) (K j)→i=j)
    (D : Finset (Finset ι))
    (hD : ∀L,L∈D ↔ BinarySecant K L ∧ 3≤L.card)
    (S : Finset (MatchingIndex ι)) :
    S∈monochromaticLines D ↔ MatchingSecant K S ∧ 3≤S.card ∧ HasOneMatching S := by
  constructor
  · intro h
    obtain ⟨⟨r,b,f,L⟩,hp,rfl⟩ := Finset.mem_image.mp h
    have hL : L∈D := by simpa [rulingParameters] using hp
    obtain ⟨hsec,hcard⟩ := (hD L).mp hL
    refine ⟨rulingSet_matchingSecant K hdet hfaith r b f L hsec,?_,r,?_⟩
    · simpa [rulingMap] using hcard
    · intro p hp
      exact (mem_rulingSet r b f L p).mp hp |>.1
  · rintro ⟨hsec,hcard,hone⟩
    obtain ⟨r,b,f,L,hL,hc,rfl⟩ := monochromatic_secant_ruling K hdet hfaith S hsec hcard hone
    apply Finset.mem_image.mpr
    refine ⟨(r,b,f,L),?_,rfl⟩
    simpa [rulingParameters] using (hD L).mpr ⟨hL,hc⟩

end
end Holant.Certificates.PlatonicIncidence
