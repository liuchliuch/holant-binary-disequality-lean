import Holant.Certificates.NormalizedDihedralQ6.Canonical

namespace Holant.Certificates.NormalizedDihedralQ6
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000

/-- Every port of an actual matching coset has a distinct constant-parity partner. -/
theorem matchingCoset_constantPartner (S : Support) (h : matchingCoset S) (i : Port) :
    ∃ j : Port, j ≠ i ∧ ∀ x ∈ S, ∀ y ∈ S, parity (i,j) x = parity (i,j) y := by
  rcases h with ⟨π,c,h⟩
  let t : Port := π.symm i
  let k : Fin 3 := ⟨t.val/2,by omega⟩
  let a : Port := ⟨2*k.val,by omega⟩
  let b : Port := ⟨2*k.val+1,by omega⟩
  have hab : a ≠ b := by intro hh; have := congrArg Fin.val hh; dsimp [a,b] at this; omega
  have ht : t = a ∨ t = b := by
    apply or_iff_not_imp_left.mpr
    intro hne
    apply Fin.ext
    have ha : t.val ≠ a.val := by exact fun hh => hne (Fin.ext hh)
    dsimp [a,b,k] at *
    omega
  have eqn (x : Word) (hx : x ∈ S) : (x (π a) ^^ x (π b)) = c k := (h x).mp hx k
  have hti : π t = i := π.apply_symm_apply i
  rcases ht with ht | ht
  · have hi : π a = i := by simpa [ht] using hti
    refine ⟨π b,?_,?_⟩
    · intro hh; exact hab (π.injective (hi.trans hh.symm))
    · intro x hx y hy
      simpa [parity,← hi] using (eqn x hx).trans (eqn y hy).symm
  · have hi : π b = i := by simpa [ht] using hti
    refine ⟨π a,?_,?_⟩
    · intro hh; exact hab (π.injective (hh.trans hi.symm))
    · intro x hx y hy
      simpa [parity,← hi,Bool.xor_comm] using (eqn x hx).trans (eqn y hy).symm

noncomputable def matchingPerm (o : Bool) : Equiv.Perm Port :=
  Equiv.ofBijective (if o then ![2,3,0,5,1,4] else ![2,3,0,4,1,5]) (by cases o <;> decide)

theorem matching_equations : ∀ o : Bool, ∀ x : Word,
    x ∈ canonicalSupport (0,false,true,o) ↔ ∀ k : Fin 3,
      (x (matchingPerm o ⟨2*k.val,by omega⟩) ^^ x (matchingPerm o ⟨2*k.val+1,by omega⟩)) = false := by decide

theorem matchingCase_fields : ∀ d : Sector,
    matchingCase d = true ↔ d.1 = 0 ∧ d.2.1 = false ∧ d.2.2.1 = true := by decide

/-- Exactly the two M entries are semantic full matching cosets. -/
theorem canonical_matching_iff (d : Sector) : matchingCoset (canonicalSupport d) ↔ matchingCase d = true := by
  constructor
  · intro hm
    by_contra hn
    have hf : matchingCase d = false := Bool.eq_false_iff.mpr hn
    rcases matchingCoset_constantPartner _ hm (isolatedPort d) with ⟨j,hj,hconst⟩
    rcases isolated_checked d hf j hj with ⟨x,hx,y,hy,hxy⟩
    exact hxy (hconst x hx y hy)
  · intro hm
    rcases d with ⟨e,a,b,o⟩
    rcases (matchingCase_fields _).mp hm with ⟨he,ha,hb⟩
    dsimp at he ha hb
    subst e; subst a; subst b
    exact ⟨matchingPerm o,fun _ => false,matching_equations o⟩

theorem printed_witness (d : Sector) (p : Pair) (γ : Bool) (n : ℕ)
    (h : printedWitness d = some (p,γ,n)) :
    p.1 < p.2 ∧ (n = 6 ∨ n = 8) ∧ injectiveProjection (canonicalSupport d) p γ ∧
      (slice (canonicalSupport d) p γ).card = n ∧ (projected (canonicalSupport d) p γ).card = n := by
  have checked := printed_entries_checked d
  rw [h] at checked
  change _ ∧ _ ∧ _ ∧ _ at checked
  exact ⟨checked.1,checked.2.1,(injectiveProjection_iff _ _ _).mpr (checked.2.2.2.trans checked.2.2.1.symm),checked.2.2⟩

theorem pair_mem : ∀ p : Pair, p.1 < p.2 → p ∈ pairs := by decide

theorem parity_swap (p : Pair) (x : Word) : parity (p.2,p.1) x = parity p x := by simp [parity,Bool.xor_comm]
theorem slice_swap (S : Support) (p : Pair) (γ : Bool) : slice S (p.2,p.1) γ = slice S p γ := by simp [slice,parity_swap]
theorem project_swap (p : Pair) : project (p.2,p.1) = project p := by funext x i; simp [project,or_comm]
theorem projected_swap (S : Support) (p : Pair) (γ : Bool) : projected S (p.2,p.1) γ = projected S p γ := by simp [projected,slice_swap,project_swap]

/-- Maximality for every genuine port pair, regardless of endpoint orientation. -/
theorem printed_maximality (d : Sector) (w : Witness) (hw : printedWitness d = some w)
    (p : Pair) (hp : p.1 ≠ p.2) (γ : Bool) (hi : injectiveProjection (canonicalSupport d) p γ) :
    (slice (canonicalSupport d) p γ).card ≤ w.2.2 := by
  have hc := printed_maximality_checked d
  rw [hw] at hc
  dsimp [EntryMaximal] at hc
  have he := (injectiveProjection_iff _ _ _).mp hi
  rcases lt_or_gt_of_ne hp with hlt | hgt
  · exact hc p (pair_mem p hlt) γ he
  · have hs := hc (p.2,p.1) (pair_mem _ hgt) γ
    simpa only [slice_swap,projected_swap] using hs (by simpa only [slice_swap,projected_swap] using he)

end Holant.Certificates.NormalizedDihedralQ6
