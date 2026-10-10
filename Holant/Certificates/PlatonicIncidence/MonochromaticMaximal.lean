import Holant.Certificates.PlatonicIncidence.MonochromaticRainbow

/-! Equivalence with the ordinary maximal-collinear-set formulation. -/
namespace Holant.Certificates.PlatonicIncidence
open Holant Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem configuration_collinear_iff_span (K : ι → BinaryMatrix)
    (hdet : ∀i,(K i).det≠0) (hfaith : ∀ i j,Proportional (K i) (K j)→i=j)
    (S : Finset (MatchingIndex ι)) (p q : MatchingIndex ι)
    (hp : p∈S) (hq : q∈S) (hpq : p≠q) :
    Projectivization.IsCollinear (configurationPoints K hdet S : Set Point) ↔
      ∀x∈S,configurationTensor K x∈Submodule.span ℂ
        ({configurationTensor K p,configurationTensor K q} : Set FourTensor) := by
  classical
  constructor
  · rintro ⟨M,hfin,hd,hm⟩
    letI := hfin
    have hv (x : MatchingIndex ι) (hx : x∈S) : configurationTensor K x∈M.submodule :=
      (Projectivization.Subspace.mem_submodule_iff M _).mpr
        (hm (Finset.mem_image.mpr ⟨x,hx,rfl⟩))
    have he := configuration_subspace_eq_pair K hdet hfaith M.submodule hd p q hpq (hv p hp) (hv q hq)
    intro x hx
    rw [←he]
    exact hv x hx
  · intro hs
    refine ⟨(Submodule.span ℂ ({configurationTensor K p,configurationTensor K q} : Set FourTensor)).projectivization,
      ?_,?_,?_⟩
    · rw [Projectivization.Subspace.submodule.apply_symm_apply]
      exact Module.Finite.span_of_finite _ (Set.toFinite _)
    · rw [Projectivization.Subspace.submodule.apply_symm_apply,
        configuration_pair_finrank K hdet hfaith p q hpq]
    · intro z hz
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
      exact (Submodule.mk_mem_projectivization_iff _ _).mpr (hs x hx)

/-- The ordinary mathematical meaning of a maximal rich collinear deck set. -/
def MaximalRichDeckLine (K : ι → BinaryMatrix) (hdet : ∀i,(K i).det≠0)
    (Q : Finset Point) : Prop :=
  Q⊆configurationPoints K hdet Finset.univ ∧ 3≤Q.card ∧
    Projectivization.IsCollinear (Q : Set Point) ∧
    ∀z∈configurationPoints K hdet Finset.univ,
      Projectivization.IsCollinear (insert z (Q : Set Point))→z∈Q

/-- Complete arbitrary-subspace intersections and maximal collinear sets are
the same actual projective geometric objects. -/
theorem actualRichLine_iff_maximal (K : ι → BinaryMatrix)
    (hdet : ∀i,(K i).det≠0) (hfaith : ∀ i j,Proportional (K i) (K j)→i=j)
    (Q : Finset Point) : ActualRichLine K hdet Q ↔ MaximalRichDeckLine K hdet Q := by
  classical
  have hinj := configurationPoint_injective K hdet hfaith
  have hmem (S : Finset (MatchingIndex ι)) (p : MatchingIndex ι) :
      configurationPoint K hdet p∈configurationPoints K hdet S ↔ p∈S :=
    Finset.mem_image.trans ⟨by
      rintro ⟨q,hq,he⟩
      exact hinj he ▸ hq,by intro hp; exact ⟨p,hp,rfl⟩⟩
  have hins (S : Finset (MatchingIndex ι)) (p : MatchingIndex ι) :
      (configurationPoints K hdet (insert p S) : Set Point)=
        insert (configurationPoint K hdet p) (configurationPoints K hdet S : Set Point) := by
    simp [configurationPoints]
  constructor
  · intro h
    obtain ⟨S,hs,hc,rfl⟩ := (actualRichLine_iff K hdet hfaith Q).mp h
    refine ⟨?_,by simpa only [configurationPoints_card K hdet hfaith] using hc,
      matchingSecant_collinear_points K hdet hfaith S hs,?_⟩
    · intro z hz
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
      exact Finset.mem_image.mpr ⟨x,Finset.mem_univ _,rfl⟩
    · intro z hz hcol
      obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨p,q,hpq,hspan⟩ := hs
      obtain ⟨hp,hq⟩ := MatchingSecant.endpoints_mem K S p q hspan
      have hcol' : Projectivization.IsCollinear (configurationPoints K hdet (insert x S) : Set Point) := by
        rw [hins]
        exact hcol
      have hx := (configuration_collinear_iff_span K hdet hfaith (insert x S) p q
        (Finset.mem_insert_of_mem hp) (Finset.mem_insert_of_mem hq) hpq).mp hcol' x (Finset.mem_insert_self _ _)
      exact (hmem S x).mpr ((hspan x).mpr hx)
  · rintro ⟨hsub,hcard,hcol,hmax⟩
    let S := Finset.univ.filter (fun p : MatchingIndex ι => configurationPoint K hdet p∈Q)
    have hS (p : MatchingIndex ι) : p∈S ↔ configurationPoint K hdet p∈Q := by simp [S]
    have heq : Q=configurationPoints K hdet S := by
      ext z
      constructor
      · intro hz
        obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp (hsub hz)
        exact Finset.mem_image.mpr ⟨x,(hS x).mpr hz,rfl⟩
      · intro hz
        obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
        exact (hS x).mp hx
    have hc : 3≤S.card := by
      rw [heq,configurationPoints_card K hdet hfaith] at hcard
      exact hcard
    obtain ⟨p,hp,q,hq,hpq⟩ := Finset.one_lt_card.mp (by omega : 1<S.card)
    have hcolS : Projectivization.IsCollinear (configurationPoints K hdet S : Set Point) := by
      rw [←heq]
      exact hcol
    have hspan := (configuration_collinear_iff_span K hdet hfaith S p q hp hq hpq).mp hcolS
    apply (actualRichLine_iff K hdet hfaith Q).mpr
    refine ⟨S,⟨p,q,hpq,?_⟩,hc,heq⟩
    intro x
    refine ⟨hspan x,?_⟩
    intro hx
    have hcol' : Projectivization.IsCollinear (configurationPoints K hdet (insert x S) : Set Point) := by
      apply (configuration_collinear_iff_span K hdet hfaith (insert x S) p q
        (Finset.mem_insert_of_mem hp) (Finset.mem_insert_of_mem hq) hpq).mpr
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl|hy
      · exact hx
      · exact hspan y hy
    apply (hS x).mpr
    apply hmax (configurationPoint K hdet x) (Finset.mem_image.mpr ⟨x,Finset.mem_univ _,rfl⟩)
    rw [heq,←hins]
    exact hcol'

end
end Holant.Certificates.PlatonicIncidence
