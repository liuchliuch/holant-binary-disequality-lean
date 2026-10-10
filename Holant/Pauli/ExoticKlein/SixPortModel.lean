import Holant.Pauli.ExoticKlein.SixPortProducts

/-! The concrete six-port problem supplied to the exact scale checker.
The bridge below is a soundness theorem, not an exhaustive certificate claim. -/
namespace Holant.Pauli.ExoticKlein.SixPort
noncomputable section
open scoped BigOperators
open LinearCertificate

 def problem (state : DirectionTriple) : Problem 4 64 16 60 48 960 where
  tensor := tensorMatrix state
  cards := cardMatrix state
  cardLines := lineVector
  cardPivot := linePivot
  targets := productVector
  targetPivot := productPivot
  live i := (cardDirections state i).isSome

 def initialRows (state : DirectionTriple) : List (Row 4) :=
  List.ofFn (fun i : Fin 4 => if (cardDirections state i).isSome then (fun _ => 0) else unitRow i)

/-- Scales on live cards are arbitrary nonzero complex numbers. Absent cards
are represented by coefficient zero, with no sampling or other scale restriction. -/
 def Admissible (state : DirectionTriple) (scale : Fin 4 → ℂ) : Prop :=
  ∀ i, if (cardDirections state i).isSome then scale i ≠ 0 else scale i = 0

 theorem admissible_live (state : DirectionTriple) (scale : Fin 4 → ℂ) (h : Admissible state scale) :
    (problem state).Live scale := by
  intro i hi
  have hh := h i
  change (cardDirections state i).isSome = true at hi
  simpa only [hi,ite_true] using hh

 theorem admissible_initialRows (state : DirectionTriple) (scale : Fin 4 → ℂ) (h : Admissible state scale) :
    Satisfies (initialRows state) scale := by
  intro row hr
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr
  have hh := h i
  split_ifs with hi
  · simp only [evaluate,map_zero,zero_mul,Finset.sum_const_zero]
  · rw [evaluate_unitRow]
    simpa [hi] using hh

 def SafeOrderedCards (h : Signature ℂ 6) : Prop := ∀ p a, OnDirection (card p a h)

 theorem safeCards_semantics (state : DirectionTriple) (scale : Fin 4 → ℂ)
    (h : SafeOrderedCards (normalizedTensor state scale)) : (problem state).SafeCards scale := by
  intro c
  obtain ⟨j,s,hs⟩ := (onDirection_iff_lines _).mp (h (contextEquiv c).1 (labelEquiv (contextEquiv c).2))
  refine ⟨j,s,?_⟩
  intro word
  exact (cardMatrix_semantics state scale c word).trans (hs word)

 def IsProduct (h : Signature ℂ 6) : Prop :=
  ∃ M : Matching (Fin 6) 3, ∃ labels : Fin 3 → Label, ∃ s : ℂ,
    s ≠ 0 ∧ h = fun x => s*M.tensor labels x

 theorem accepted_semantics (state : DirectionTriple) (scale : Fin 4 → ℂ)
    (h : (problem state).Accepted scale) (hn : normalizedTensor state scale ≠ 0) :
    IsProduct (normalizedTensor state scale) := by
  obtain ⟨j,s,hs⟩ := h
  have he : normalizedTensor state scale = fun x => s*productTensor (productDirectionEquiv j) x := by
    funext x
    have hx := hs (wordEquiv 6 x)
    change output (tensorMatrix state) scale _ = s*Algebraic.gaussianToComplex (productVector j _) at hx
    simpa only [tensorMatrix_semantics,productVector_semantics,Equiv.symm_apply_apply] using hx
  have hs0 : s ≠ 0 := by
    intro hz
    apply hn
    rw [he,hz]
    funext x
    simp
  refine ⟨productMatching (productDirectionEquiv j).1 (productDirectionEquiv j).2.2.1,
    productLabels (productDirectionEquiv j),s,hs0,?_⟩
  rw [he,productTensor_matching]

/-- A checked certificate for a particular direction triple proves the full
arbitrary-complex-scale claim for that triple. Exhaustive triple coverage is a
separate finite obligation, not a hypothesis hidden inside this checker. -/
 theorem normalized_product_of_checked (state : DirectionTriple) (certificate : Certificate 4 64 60 48 960)
    (hc : certificate.check (problem state) (initialRows state) = true)
    (scale : Fin 4 → ℂ) (ha : Admissible state scale)
    (hs : SafeOrderedCards (normalizedTensor state scale)) (hn : normalizedTensor state scale ≠ 0) :
    IsProduct (normalizedTensor state scale) := by
  apply accepted_semantics state scale _ hn
  exact certificate.sound (problem state) (initialRows state) hc scale
    (admissible_initialRows state scale ha) (admissible_live state scale ha) (safeCards_semantics state scale hs)

/-- No output targets are needed for a stratum certified impossible. -/
def refutationProblem (state : DirectionTriple) : Problem 4 64 16 60 48 0 where
  tensor := tensorMatrix state
  cards := cardMatrix state
  cardLines := lineVector
  cardPivot := linePivot
  targets i := i.elim0
  targetPivot i := i.elim0
  live i := (cardDirections state i).isSome

 theorem normalized_not_safe_of_refutation (state : DirectionTriple) (certificate : Certificate 4 64 60 48 0)
    (hc : certificate.check (refutationProblem state) (initialRows state) = true)
    (scale : Fin 4 → ℂ) (ha : Admissible state scale) :
    ¬SafeOrderedCards (normalizedTensor state scale) := by
  intro hs
  have h := certificate.sound (refutationProblem state) (initialRows state) hc scale
    (admissible_initialRows state scale ha) (admissible_live state scale ha) (safeCards_semantics state scale hs)
  obtain ⟨j,_,_⟩ := h
  exact j.elim0

end
end Holant.Pauli.ExoticKlein.SixPort
