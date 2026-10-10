import Holant.Proofs.BinaryInterpolation.EffectiveRecognition.NullstellensatzSearch.Completeness


namespace Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.NullstellensatzSearch
open Holant.Tractable Holant.LocalDrafts.EffectiveAlgebraic
variable {m n q : ℕ}

def candidateAt (m n q index : ℕ) : Option (Candidate m n q) :=
  (tupleAt (α := Candidate m n q) 1 index).map (fun t => t 0)

def candidates (m n q height : ℕ) : List (Candidate m n q) :=
  (tuplesThrough (α := Candidate m n q) 1 height).map (fun t => t 0)

theorem candidateAt_encode (r : Candidate m n q) :
    candidateAt m n q (Encodable.encode (fun _ : Fin 1 => r)) = some r := by
  simp [candidateAt]

theorem candidates_complete (r : Candidate m n q) :
    r ∈ candidates m n q (Encodable.encode (fun _ : Fin 1 => r)) :=
  List.mem_map.mpr ⟨fun _ : Fin 1 => r, tuplesThrough_complete _, rfl⟩

theorem candidates_mono {a b : ℕ} (h : a ≤ b) :
    ∀ r ∈ candidates m n q a, r ∈ candidates m n q b := by
  intro r hr
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hr
  exact List.mem_map.mpr ⟨t, tuplesThrough_mono h t ht, rfl⟩

def searchThrough (target : Fin m → RootCode) (S : EncodedSystem.System m n)
    (height : ℕ) : Option (Candidate m n S.length) :=
  (candidates m n S.length height).find? (check target S)

theorem searchThrough_checked (target : Fin m → RootCode) (S : EncodedSystem.System m n)
    (height : ℕ) (r : Candidate m n S.length) (hr : searchThrough target S height = some r) :
    check target S r = true := List.find?_some hr

theorem searchThrough_sound (target : Fin m → RootCode) (w : Fin m → ℂ)
    (ht : ∀ i, (target i).Represents (w i)) (S : EncodedSystem.System m n)
    (height : ℕ) (r : Candidate m n S.length) (hr : searchThrough target S height = some r) :
    ¬ ∃ x : Fin n → ℂ, ∀ e ∈ S, MvPolynomial.aeval x (EncodedSystem.polynomial w e) = 0 :=
  check_sound target w ht S r (searchThrough_checked target S height r hr)

theorem exists_code_checked (w : Fin m → AlgebraicComplex) (target : Fin m → RootCode)
    (ht : ∀ i, (target i).Represents (w i : ℂ)) (S : EncodedSystem.System m n)
    (hn : NoAlgebraicSolution w S) :
    ∃ (index : ℕ) (r : Candidate m n S.length), candidateAt m n S.length index = some r ∧
      r ∈ candidates m n S.length index ∧ check target S r = true := by
  obtain ⟨r, hr⟩ := exists_checked w target ht S hn
  exact ⟨Encodable.encode (fun _ : Fin 1 => r), r, candidateAt_encode r, candidates_complete r, hr⟩

/-- Every sufficiently large finite stage finds a negative certificate. The
no-solution premise is used only in this semantic theorem, not by the program. -/
theorem eventually_some (w : Fin m → AlgebraicComplex) (target : Fin m → RootCode)
    (ht : ∀ i, (target i).Represents (w i : ℂ)) (S : EncodedSystem.System m n)
    (hn : NoAlgebraicSolution w S) :
    ∃ height, ∀ h ≥ height, (searchThrough target S h).isSome = true := by
  obtain ⟨index, r, _, hmem, hr⟩ := exists_code_checked w target ht S hn
  refine ⟨index, fun h hh => ?_⟩
  exact List.find?_isSome.mpr ⟨r, candidates_mono hh r hmem, hr⟩

theorem eventually_some_of_noComplex (w : Fin m → AlgebraicComplex) (target : Fin m → RootCode)
    (ht : ∀ i, (target i).Represents (w i : ℂ)) (S : EncodedSystem.System m n)
    (hn : ¬ ∃ x : Fin n → ℂ, ∀ e ∈ S,
      MvPolynomial.aeval x (EncodedSystem.polynomial (fun i => (w i : ℂ)) e) = 0) :
    ∃ height, ∀ h ≥ height, (searchThrough target S h).isSome = true :=
  eventually_some w target ht S (noAlgebraic_of_noComplex w S hn)

end Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.NullstellensatzSearch
