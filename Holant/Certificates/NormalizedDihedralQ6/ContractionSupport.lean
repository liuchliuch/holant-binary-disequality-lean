import Holant.Certificates.NormalizedDihedralQ6.ContractionCoordinates
import Holant.OpenNetwork

/-! The actual I/X contraction sum has precisely one surviving nonzero summand
above each projected word when the selected support projection is injective. -/
namespace Holant.Certificates.NormalizedDihedralQ6
open Holant
set_option backward.isDefEq.respectTransparency false

variable {K : Type*} [CommSemiring K]

def parityEdge (γ : Bool) : EdgeKind := if γ then .disequality else .equality

@[simp] theorem parityEdge_false : parityEdge false = .equality := rfl
@[simp] theorem parityEdge_true : parityEdge true = .disequality := rfl

def parityKernel (γ : Bool) : Bool → Bool → K := (parityEdge γ).value

theorem parityKernel_eq (γ a b : Bool) :
    parityKernel (K := K) γ a b = if (a ^^ b) = γ then 1 else 0 := by
  cases γ <;> cases a <;> cases b <;> simp [parityKernel,parityEdge,EdgeKind.value,Signature.equality,Signature.disequality]

@[simp] theorem parityKernel_false : parityKernel (K := K) false = Signature.equality := rfl
@[simp] theorem parityKernel_true : parityKernel (K := K) true = Signature.disequality := rfl

def contractAt (h : Signature K 6) (p : Pair) (hp : p.1 ≠ p.2) (γ : Bool) : Signature K 4 :=
  Signature.contract (parityKernel γ) (Tensor.reindex (orderedPorts p hp).symm h)

def summand (h : Signature K 6) (p : Pair) (hp : p.1 ≠ p.2) (γ : Bool)
    (x : Fin 4 → Bool) (ab : Bool × Bool) : K :=
  parityKernel γ ab.1 ab.2 * h (joinWord p hp ab.1 ab.2 x)

theorem contractAt_sum (h : Signature K 6) (p : Pair) (hp : p.1 ≠ p.2) (γ : Bool) (x : Fin 4 → Bool) :
    contractAt h p hp γ x = ∑ ab : Bool × Bool, summand h p hp γ x ab := by
  rw [Fintype.sum_prod_type]
  rfl

theorem summand_nonzero_iff (h : Signature K 6) (S : Support)
    (hs : ∀ y, h y ≠ 0 ↔ y ∈ S) (p : Pair) (hp : p.1 ≠ p.2) (γ : Bool)
    (x : Fin 4 → Bool) (ab : Bool × Bool) :
    summand h p hp γ x ab ≠ 0 ↔ joinWord p hp ab.1 ab.2 x ∈ slice S p γ := by
  constructor
  · intro ht
    rw [summand,parityKernel_eq] at ht
    split_ifs at ht with he
    · refine Finset.mem_filter.mpr ⟨(hs _).mp (by simpa only [one_mul] using ht),?_⟩
      simpa only [parity,joinWord_first,joinWord_second] using he
    · simp only [zero_mul,ne_eq,not_true_eq_false] at ht
  · intro ht
    rcases Finset.mem_filter.mp ht with ⟨hy,hγ⟩
    have he : (ab.1 ^^ ab.2) = γ := by
      simpa only [parity,joinWord_first,joinWord_second] using hγ
    simpa only [summand,parityKernel_eq,he,ite_true,one_mul] using (hs _).mpr hy

theorem summand_value (h : Signature K 6) (p : Pair) (hp : p.1 ≠ p.2) (γ : Bool)
    (x : Fin 4 → Bool) (ab : Bool × Bool)
    (he : parity p (joinWord p hp ab.1 ab.2 x) = γ) :
    summand h p hp γ x ab = h (joinWord p hp ab.1 ab.2 x) := by
  simp only [parity,joinWord_first,joinWord_second] at he
  simp [summand,parityKernel_eq,he]

/-- Distinct internal endpoint assignments cannot both survive over the same external word. -/
theorem nonzero_summand_unique (h : Signature K 6) (S : Support)
    (hs : ∀ y, h y ≠ 0 ↔ y ∈ S) (p : Pair) (hp : p.1 ≠ p.2) (γ : Bool)
    (hi : injectiveProjection S p γ) (x : Fin 4 → Bool) (ab cd : Bool × Bool)
    (hab : summand h p hp γ x ab ≠ 0) (hcd : summand h p hp γ x cd ≠ 0) : ab = cd := by
  have ha := (summand_nonzero_iff h S hs p hp γ x ab).mp hab
  have hc := (summand_nonzero_iff h S hs p hp γ x cd).mp hcd
  have he : project p (joinWord p hp ab.1 ab.2 x) = project p (joinWord p hp cd.1 cd.2 x) := by
    apply (external_eq_iff_project_eq p hp _ _).mp
    simp
  have hh := hi ha hc he
  apply Prod.ext
  · have hz := congrFun hh p.1
    simpa using hz
  · have hz := congrFun hh p.2
    simpa using hz

/-- An external word is in the projected support exactly when it has a surviving summand. -/
theorem image_iff_nonzero_summand (h : Signature K 6) (S : Support)
    (hs : ∀ y, h y ≠ 0 ↔ y ∈ S) (p : Pair) (hp : p.1 ≠ p.2) (γ : Bool)
    (x : Fin 4 → Bool) :
    x ∈ (slice S p γ).image (externalWord p hp) ↔ ∃ ab, summand h p hp γ x ab ≠ 0 := by
  constructor
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨y,hy,rfl⟩
    refine ⟨(y p.1,y p.2),?_⟩
    rw [summand_nonzero_iff h S hs p hp γ,joinWord_external]
    exact hy
  · rintro ⟨ab,hab⟩
    exact Finset.mem_image.mpr ⟨joinWord p hp ab.1 ab.2 x,
      (summand_nonzero_iff h S hs p hp γ x ab).mp hab,external_joinWord p hp _ _ x⟩

/-- Above every projected word, the actual contraction is exactly one original nonzero coefficient. -/
theorem cancellation_free (h : Signature K 6) (S : Support)
    (hs : ∀ y, h y ≠ 0 ↔ y ∈ S) (p : Pair) (hp : p.1 ≠ p.2) (γ : Bool)
    (hi : injectiveProjection S p γ) (x : Fin 4 → Bool)
    (hx : x ∈ (slice S p γ).image (externalWord p hp)) :
    ∃ ab : Bool × Bool, summand h p hp γ x ab ≠ 0 ∧
      (∀ cd, summand h p hp γ x cd ≠ 0 → cd = ab) ∧
      contractAt h p hp γ x = summand h p hp γ x ab ∧
      summand h p hp γ x ab = h (joinWord p hp ab.1 ab.2 x) := by
  rcases (image_iff_nonzero_summand h S hs p hp γ x).mp hx with ⟨ab,hab⟩
  have hu : ∀ cd, summand h p hp γ x cd ≠ 0 → cd = ab :=
    fun cd hcd => nonzero_summand_unique h S hs p hp γ hi x cd ab hcd hab
  refine ⟨ab,hab,hu,?_,?_⟩
  · rw [contractAt_sum]
    apply Fintype.sum_eq_single ab
    intro cd hne
    by_contra hn
    exact hne (hu cd hn)
  · apply summand_value
    exact (Finset.mem_filter.mp ((summand_nonzero_iff h S hs p hp γ x ab).mp hab)).2

/-- There is no cancellation or accidental extra support after actual contraction. -/
theorem contractAt_support (h : Signature K 6) (S : Support)
    (hs : ∀ y, h y ≠ 0 ↔ y ∈ S) (p : Pair) (hp : p.1 ≠ p.2) (γ : Bool)
    (hi : injectiveProjection S p γ) (x : Fin 4 → Bool) :
    contractAt h p hp γ x ≠ 0 ↔ x ∈ (slice S p γ).image (externalWord p hp) := by
  constructor
  · intro hx
    by_contra hn
    have hz : ∀ ab, summand h p hp γ x ab = 0 := by
      intro ab
      by_contra ha
      exact hn ((image_iff_nonzero_summand h S hs p hp γ x).mpr ⟨ab,ha⟩)
    rw [contractAt_sum] at hx
    simp only [hz,Finset.sum_const_zero] at hx
    exact hx rfl
  · intro hx
    rcases cancellation_free h S hs p hp γ hi x hx with ⟨ab,hab,_,he,_⟩
    rwa [he]

open scoped Classical in
theorem contractAt_support_card (h : Signature K 6) (S : Support)
    (hs : ∀ y, h y ≠ 0 ↔ y ∈ S) (p : Pair) (hp : p.1 ≠ p.2) (γ : Bool)
    (hi : injectiveProjection S p γ) :
    ((Finset.univ : Finset (Fin 4 → Bool)).filter (fun x => contractAt h p hp γ x ≠ 0)).card =
      (projected S p γ).card := by
  have he : ((Finset.univ : Finset (Fin 4 → Bool)).filter (fun x => contractAt h p hp γ x ≠ 0)) =
      (slice S p γ).image (externalWord p hp) := by
    ext x
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,contractAt_support h S hs p hp γ hi]
  rw [he]
  exact external_image_card S p hp γ

end Holant.Certificates.NormalizedDihedralQ6
