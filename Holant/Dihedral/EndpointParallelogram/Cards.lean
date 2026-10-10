import Holant.Dihedral.EndpointParallelogram.Matching
import Holant.Realization
import Mathlib.Algebra.Field.Defs

/-! Actual phase-card supports are derived from the four endpoint slices,
including their recorded nonzero representative scalars. -/
namespace Holant.Dihedral.EndpointParallelogram
open Holant

variable {V K : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Field K]

def pencil (f g : V → K) (t κ : K) : V → K := fun x => κ * (f x + t * g x)

def fullCoset (f : V → K) (L : Submodule (ZMod 2) V) (a : V) : Prop :=
  ∀ x, f x ≠ 0 ↔ x ∈ coset L a

/-- The actual phase sum has full support on the union. No cancellation premise
is needed: it follows from the complementary endpoint cosets. -/
theorem pencil_support (L : Submodule (ZMod 2) V) (a b : V) (f g : V → K)
    (hf : fullCoset f L a) (hg : fullCoset g L b) (hab : a+b ∉ L)
    (t κ : K) (ht : t ≠ 0) (hκ : κ ≠ 0) (x : V) :
    pencil f g t κ x ≠ 0 ↔ x ∈ coset (extension L (a+b)) a := by
  have hd := Set.disjoint_left.mp (cosets_disjoint L a b hab)
  have hu := congrArg (fun s : Set V => x ∈ s) (coset_union L a b)
  change (x ∈ coset L a ∨ x ∈ coset L b) = _ at hu
  rw [← hu]
  by_cases ha : f x = 0
  · simp only [pencil,ha,zero_add,mul_ne_zero_iff,hκ,true_and,ht,Ne,not_false_eq_true]
    have hh : x ∉ coset L a := by intro hx; exact (hf x).mpr hx ha
    simp only [hh,false_or]
    exact hg x
  · have ha' := (hf x).mp ha
    have hb : g x = 0 := by
      by_contra hn
      exact hd ha' ((hg x).mp hn)
    simp [pencil,hb,ha,hκ,ha']

/-- Every nonzero phase gives a nonzero actual card, even when arbitrary
coefficients and arbitrary nonzero physical representative scalars are used. -/
theorem pencil_nonzero (L : Submodule (ZMod 2) V) (a b : V) (f g : V → K)
    (hf : fullCoset f L a) (hg : fullCoset g L b) (hab : a+b ∉ L)
    (t κ : K) (ht : t ≠ 0) (hκ : κ ≠ 0) : pencil f g t κ ≠ 0 := by
  intro h
  have hn := (pencil_support L a b f g hf hg hab t κ ht hκ a).mpr
    (by simp [coset,ZModModule.add_self])
  exact hn (congrFun h a)

/-- Exact source endpoint test, at arbitrary nonzero actual phase samples.
The matching witnesses describe the actual cards themselves, not endpoints. -/
theorem actual_card_endpoint_test {ι : Type*} [DecidableEq ι]
    (L : Submodule (ZMod 2) (ι → ZMod 2)) (a b c d : ι → ZMod 2)
    (A B C D : (ι → ZMod 2) → K)
    (hA : fullCoset A L a) (hB : fullCoset B L b)
    (hC : fullCoset C L c) (hD : fullCoset D L d)
    (hE : a+d ∉ L) (hO : b+c ∉ L)
    (t s κE κO : K) (ht : t ≠ 0) (hs : s ≠ 0) (hκE : κE ≠ 0) (hκO : κO ≠ 0)
    (ME MO : Pairing ι) (e o : ι → ZMod 2)
    (hmE : fullCoset (pencil A D t κE) ME.code e)
    (hmO : fullCoset (pencil B C s κO) MO.code o) :
    ME = MO ↔ a+b+c+d ∈ L := by
  have hE' : extension L (a+d) = ME.code := by
    apply coset_direction_unique _ _ a e
    ext x
    exact (pencil_support L a d A D hA hD hE t κE ht hκE x).symm.trans (hmE x)
  have hO' : extension L (b+c) = MO.code := by
    apply coset_direction_unique _ _ b o
    ext x
    exact (pencil_support L b c B C hB hC hO s κO hs hκO x).symm.trans (hmO x)
  rw [← Pairing.code_eq_iff,← hE',← hO']
  exact parallelogram_iff L a b c d hE hO

end Holant.Dihedral.EndpointParallelogram
