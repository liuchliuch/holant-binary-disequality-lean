import Holant.Certificates.NormalizedDihedralQ6.Data

/-! Exact support covariance under a port permutation and independent bit flips.
These are bijections of actual Boolean words; injective projected slices and
semantic perfect-matching cosets are transported, not approximated by counts. -/

namespace Holant.Certificates.NormalizedDihedralQ6

private theorem xor_twist_iff (a b c d e : Bool) :
    ((a ^^ c) ^^ (b ^^ d)) = e ↔ (a ^^ b) = (e ^^ c ^^ d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> decide
private theorem xor_twist_cancel_iff (a b c d e : Bool) :
    ((a ^^ c) ^^ (b ^^ d)) = (e ^^ c ^^ d) ↔ (a ^^ b) = e := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> decide
private theorem xor_right_cancel_iff (a b c : Bool) : (a ^^ c) = (b ^^ c) ↔ a = b := by
  cases a <;> cases b <;> cases c <;> decide

/-- New coordinate j is old coordinate π j, followed by its literal flip bit. -/
def wordEquiv (π : Equiv.Perm Port) (δ : Word) : Word ≃ Word where
  toFun x j := x (π j) ^^ δ j
  invFun y i := y (π.symm i) ^^ δ (π.symm i)
  left_inv x := by funext i; simp
  right_inv y := by funext j; simp

@[simp] theorem wordEquiv_apply (π : Equiv.Perm Port) (δ : Word) (x : Word) (j : Port) :
    wordEquiv π δ x j = (x (π j) ^^ δ j) := rfl
@[simp] theorem wordEquiv_symm_apply (π : Equiv.Perm Port) (δ : Word) (y : Word) (i : Port) :
    (wordEquiv π δ).symm y i = (y (π.symm i) ^^ δ (π.symm i)) := rfl

def transform (π : Equiv.Perm Port) (δ : Word) (S : Support) : Support := S.image (wordEquiv π δ)

@[simp] theorem mem_transform (π : Equiv.Perm Port) (δ : Word) (S : Support) (y : Word) :
    y ∈ transform π δ S ↔ (wordEquiv π δ).symm y ∈ S := by
  constructor
  · intro hy
    obtain ⟨x,hx,hxy⟩ := Finset.mem_image.mp hy
    rw [← hxy]
    simpa using hx
  · intro hy
    exact Finset.mem_image.mpr ⟨(wordEquiv π δ).symm y,hy,(wordEquiv π δ).apply_symm_apply y⟩

/-- A full matching-coset equality is preserved, not only equations on its support. -/
theorem matchingCoset_transform (π : Equiv.Perm Port) (δ : Word) (S : Support)
    (hS : matchingCoset S) : matchingCoset (transform π δ S) := by
  obtain ⟨σ,c,hS⟩ := hS
  let τ := σ.trans π.symm
  refine ⟨τ, fun k => c k ^^ δ (τ ⟨2*k.val,by omega⟩) ^^ δ (τ ⟨2*k.val+1,by omega⟩), ?_⟩
  intro y
  rw [mem_transform, hS]
  constructor
  · intro hy k
    exact (xor_twist_iff _ _ _ _ _).mp (hy k)
  · intro hy k
    exact (xor_twist_iff _ _ _ _ _).mpr (hy k)

theorem transform_inverse (π : Equiv.Perm Port) (δ : Word) (S : Support) :
    transform π.symm (fun i => δ (π.symm i)) (transform π δ S) = S := by
  have hi : wordEquiv π.symm (fun i => δ (π.symm i)) = (wordEquiv π δ).symm := by
    apply Equiv.ext
    intro y
    rfl
  simp only [transform, hi, Finset.image_image, Function.comp_def, Equiv.symm_apply_apply]
  exact Finset.image_id

theorem matchingCoset_transform_iff (π : Equiv.Perm Port) (δ : Word) (S : Support) :
    matchingCoset (transform π δ S) ↔ matchingCoset S := by
  constructor
  · intro h
    have hh := matchingCoset_transform π.symm (fun i => δ (π.symm i)) _ h
    rwa [transform_inverse] at hh
  · exact matchingCoset_transform π δ S

/-- Pair orientation does not affect the physical equality/disequality condition. -/
theorem parity_transform_iff (π : Equiv.Perm Port) (δ : Word) (p : Pair) (γ : Bool) (x : Word) :
    parity p (wordEquiv π δ x) = (γ ^^ δ p.1 ^^ δ p.2) ↔ parity (π p.1,π p.2) x = γ :=
  xor_twist_cancel_iff _ _ _ _ _

theorem slice_transform (π : Equiv.Perm Port) (δ : Word) (S : Support) (p : Pair) (γ : Bool) :
    slice (transform π δ S) p (γ ^^ δ p.1 ^^ δ p.2) =
      transform π δ (slice S (π p.1,π p.2) γ) := by
  ext y
  simp only [slice, Finset.mem_filter, transform, Finset.mem_image]
  constructor
  · rintro ⟨⟨x,hx,rfl⟩,hp⟩
    exact ⟨x, ⟨hx,(parity_transform_iff π δ p γ x).mp hp⟩,rfl⟩
  · rintro ⟨x,⟨hx,hp⟩,rfl⟩
    exact ⟨⟨x,hx,rfl⟩,(parity_transform_iff π δ p γ x).mpr hp⟩

theorem slice_card_transform (π : Equiv.Perm Port) (δ : Word) (S : Support) (p : Pair) (γ : Bool) :
    (slice (transform π δ S) p (γ ^^ δ p.1 ^^ δ p.2)).card =
      (slice S (π p.1,π p.2) γ).card := by
  rw [slice_transform]
  exact Finset.card_image_of_injective _ (wordEquiv π δ).injective

/-- Equality after deletion is exactly agreement on all undeleted coordinates. -/
theorem project_eq_iff (p : Pair) (x y : Word) :
    project p x = project p y ↔ ∀ i, i ≠ p.1 → i ≠ p.2 → x i = y i := by
  constructor
  · intro h i hi hj
    have hh := congrFun h i
    simpa [project, hi, hj] using hh
  · intro h
    funext i
    by_cases hi : i = p.1 ∨ i = p.2
    · simp [project,hi]
    · simp only [not_or] at hi
      simpa [project,hi.1,hi.2] using h i hi.1 hi.2

/-- Every projection fibre is preserved under the actual word bijection. -/
theorem project_transform_eq_iff (π : Equiv.Perm Port) (δ : Word) (p : Pair) (x y : Word) :
    project p (wordEquiv π δ x) = project p (wordEquiv π δ y) ↔
      project (π p.1,π p.2) x = project (π p.1,π p.2) y := by
  rw [project_eq_iff,project_eq_iff]
  constructor
  · intro h i hi hj
    have hi' : π.symm i ≠ p.1 := by intro hh; apply hi; simpa using congrArg π hh
    have hj' : π.symm i ≠ p.2 := by intro hh; apply hj; simpa using congrArg π hh
    have hh := h (π.symm i) hi' hj'
    simp only [wordEquiv_apply, Equiv.apply_symm_apply] at hh
    exact (xor_right_cancel_iff _ _ _).mp hh
  · intro h j hi hj
    have hi' : π j ≠ π p.1 := fun hh => hi (π.injective hh)
    have hj' : π j ≠ π p.2 := fun hh => hj (π.injective hh)
    exact congrArg (fun b => b ^^ δ j) (h (π j) hi' hj')

theorem injectiveProjection_transform_iff (π : Equiv.Perm Port) (δ : Word) (S : Support)
    (p : Pair) (γ : Bool) :
    injectiveProjection (transform π δ S) p (γ ^^ δ p.1 ^^ δ p.2) ↔
      injectiveProjection S (π p.1,π p.2) γ := by
  unfold injectiveProjection
  rw [slice_transform]
  constructor
  · intro h x hx y hy hxy
    apply (wordEquiv π δ).injective
    apply h
    · exact Finset.mem_image.mpr ⟨x,hx,rfl⟩
    · exact Finset.mem_image.mpr ⟨y,hy,rfl⟩
    · exact (project_transform_eq_iff π δ p x y).mpr hxy
  · intro h x hx y hy hxy
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hy
    exact congrArg (wordEquiv π δ) (h hu hv ((project_transform_eq_iff π δ p u v).mp hxy))

end Holant.Certificates.NormalizedDihedralQ6
