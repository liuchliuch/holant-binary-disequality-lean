import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Abel

/-! The exact binary linear-algebra content of the endpoint test. No matching
or actual-card equality is supplied as a hypothesis. -/
namespace Holant.Dihedral.EndpointParallelogram

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

def extension (L : Submodule (ZMod 2) V) (d : V) : Submodule (ZMod 2) V :=
  L ⊔ Submodule.span (ZMod 2) {d}

def coset (L : Submodule (ZMod 2) V) (a : V) : Set V := {x | x + a ∈ L}

private theorem cancel (x y : V) : x + y + y = x := by
  rw [add_assoc,ZModModule.add_self,add_zero]

/-- Over F₂ adjoining d adds exactly one coset. -/
theorem mem_extension (L : Submodule (ZMod 2) V) (d x : V) :
    x ∈ extension L d ↔ x ∈ L ∨ x + d ∈ L := by
  constructor
  · intro hx
    obtain ⟨l,hl,v,hv,rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hv
    have hc : c = 0 ∨ c = 1 := by
      fin_cases c
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hc with rfl | rfl
    · exact Or.inl (by simpa using hl)
    · exact Or.inr (by simpa only [one_smul,cancel] using hl)
  · rintro (hx | hx)
    · exact (show L ≤ extension L d from le_sup_left) hx
    · have hd : d ∈ extension L d := (show Submodule.span (ZMod 2) {d} ≤ extension L d from le_sup_right) (Submodule.mem_span_singleton_self d)
      have hx' : x + d ∈ extension L d := (show L ≤ extension L d from le_sup_left) hx
      simpa only [cancel] using (extension L d).add_mem hx' hd

/-- Two genuine one-dimensional extensions agree exactly when their two
nonzero quotient classes agree; this is special to the binary field. -/
theorem extension_eq_iff (L : Submodule (ZMod 2) V) (d e : V)
    (hd : d ∉ L) (he : e ∉ L) :
    extension L d = extension L e ↔ d + e ∈ L := by
  constructor
  · intro h
    have hm : d ∈ extension L e := h ▸ (show Submodule.span (ZMod 2) {d} ≤ extension L d from le_sup_right) (Submodule.mem_span_singleton_self d)
    exact ((mem_extension L e d).mp hm).resolve_left hd
  · intro h
    apply le_antisymm
    · apply sup_le le_sup_left
      apply (Submodule.span_singleton_le_iff_mem _ _).mpr
      exact (mem_extension L e d).mpr (Or.inr h)
    · apply sup_le le_sup_left
      apply (Submodule.span_singleton_le_iff_mem _ _).mpr
      exact (mem_extension L d e).mpr (Or.inr (by simpa only [add_comm] using h))

/-- Literal four-offset form of the manuscript parallelogram equation. -/
theorem parallelogram_iff (L : Submodule (ZMod 2) V) (a b c d : V)
    (he : a + d ∉ L) (ho : b + c ∉ L) :
    extension L (a+d) = extension L (b+c) ↔ a+b+c+d ∈ L := by
  rw [extension_eq_iff L (a+d) (b+c) he ho]
  have hh : a+d+(b+c) = a+b+c+d := by abel
  rw [hh]

/-- Changing any endpoint representative within its own L-coset does not
change the source test. -/
theorem representatives_iff (L : Submodule (ZMod 2) V) (a b c d l₀ l₁ l₂ l₃ : V)
    (h₀ : l₀ ∈ L) (h₁ : l₁ ∈ L) (h₂ : l₂ ∈ L) (h₃ : l₃ ∈ L) :
    (a+l₀)+(b+l₁)+(c+l₂)+(d+l₃) ∈ L ↔ a+b+c+d ∈ L := by
  have hh : l₀+l₁+l₂+l₃ ∈ L := L.add_mem (L.add_mem (L.add_mem h₀ h₁) h₂) h₃
  have he : (a+l₀)+(b+l₁)+(c+l₂)+(d+l₃) = (a+b+c+d)+(l₀+l₁+l₂+l₃) := by abel
  rw [he]
  constructor
  · intro h
    simpa only [cancel] using L.add_mem h hh
  · intro h
    exact L.add_mem h hh

/-- Distinct endpoint cosets do not overlap, so an actual nonzero phase
cannot cancel the two endpoint contributions. -/
theorem cosets_disjoint (L : Submodule (ZMod 2) V) (a b : V) (hab : a+b ∉ L) :
    Disjoint (coset L a) (coset L b) := by
  rw [Set.disjoint_left]
  intro x ha hb
  apply hab
  have hh := L.add_mem ha hb
  have he : (x+a)+(x+b)=a+b := by
    calc
      (x+a)+(x+b) = (a+x)+(x+b) := by rw [add_comm x a]
      _ = a+b := ZModModule.add_add_add_cancel a x b
  rwa [he] at hh

/-- The union of the two endpoint cosets is the actual card's affine space. -/
theorem coset_union (L : Submodule (ZMod 2) V) (a b : V) :
    coset L a ∪ coset L b = coset (extension L (a+b)) a := by
  ext x
  simp only [Set.mem_union,coset,Set.mem_setOf_eq,mem_extension]
  have he : x+a+(a+b)=x+b := ZModModule.add_add_add_cancel x a b
  rw [he]

/-- An affine set determines its linear direction. -/
theorem coset_direction_unique (L M : Submodule (ZMod 2) V) (a b : V)
    (h : coset L a = coset M b) : L = M := by
  have hab : a+b ∈ M := by
    have ha : a ∈ coset L a := by simp [coset,ZModModule.add_self]
    change a ∈ coset M b
    rw [← h]
    exact ha
  have hba : b+a ∈ L := by
    have hb : b ∈ coset M b := by simp [coset,ZModModule.add_self]
    change b ∈ coset L a
    rw [h]
    exact hb
  apply le_antisymm
  · intro x hx
    have ha : x+a ∈ coset L a := by simpa only [coset,Set.mem_setOf_eq,cancel] using hx
    have hb : (x+a)+b ∈ M := by
      change x+a ∈ coset M b
      rw [← h]
      exact ha
    have hh := M.add_mem hb hab
    have he : (x+a+b)+(a+b)=x := by
      rw [add_assoc x a b,cancel]
    rwa [he] at hh
  · intro x hx
    have hb : x+b ∈ coset M b := by simpa only [coset,Set.mem_setOf_eq,cancel] using hx
    have ha : (x+b)+a ∈ L := by
      change x+b ∈ coset L a
      rw [h]
      exact hb
    have hh := L.add_mem ha hba
    have he : (x+b+a)+(b+a)=x := by
      rw [add_assoc x b a,cancel]
    rwa [he] at hh

end Holant.Dihedral.EndpointParallelogram
