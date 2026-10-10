import Holant.Proofs.Closure.ClosureSixPortSupportOrder
import Holant.Proofs.Closure.ClosureSixPortZero
import Holant.Proofs.Closure.ClosureRootPencilProduct

/-! NEW UNVERIFIED actual four-flat contradiction. Root-card presentations
have exactly four support words; unique-lift six/eight cards are impossible.
The surviving matching coset yields a literal vanished parity sector. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSixPort
open Holant Holant.Projective

/-- Four nonzero entries follows from the actual matching presentation and
its nonsingular factors, without a supplied fixed matching. -/
theorem rootMatching_four_support {m : ℕ} (q : Signature ℂ 4) (matching : RootMatching m q) :
    (ClosureRootPencil.support q).card = 4 := by
  rcases matching with ⟨M,mono,scalar,equation⟩
  obtain ⟨D⟩ := ClosureRootPencil.of_presentation M mono scalar equation
  exact D.support_card

/-- The normalized table's six/eight ACTUAL cards contradict the literal
ordered deck predicate, including its zero branch. -/
theorem normalized_atlas_forces_matching {m : ℕ} (h : Signature ℂ 6)
    (deck : OrderedRootDeck m h) (edge : Fin 6) (a b o : Bool)
    (support : ∀ w, h w ≠ 0 ↔ w ∈ flatSupport edge a b o) :
    edge=0 ∧ a=false ∧ b=true := by
  by_contra notMatching
  obtain ⟨e,p,T,card,supported⟩ := normalized_actual_card_support edge a b o notMatching h support
  have same : ClosureRootPencil.support (phaseCard h e p 1) = T := by
    ext x
    simp only [ClosureRootPencil.support,Finset.mem_filter,Finset.mem_univ,true_and]
    exact supported x
  rcases deck e p 1 (one_pow m) with zero | matching
  · have empty : T = ∅ := by
      rw [←same,zero]
      ext x
      simp [ClosureRootPencil.support]
    rw [empty] at card
    simp at card
  · have four := rootMatching_four_support _ matching
    rw [same] at four
    omega

/-- The two exceptional atlas entries expose an actual zero sector at one
edge of their three-edge matching, independently of the coefficients. -/
theorem normalized_matching_zero_sector (h : Signature ℂ 6) (o : Bool)
    (support : ∀ w, h w ≠ 0 ↔ w ∈ nativeMatchingSupport o) :
    ∃ e : Equiv.Perm (Fin 6), ZeroSector h e true := by
  let j : Fin 6 := if o then 5 else 4
  have distinct : (0 : Fin 6) ≠ j := by cases o <;> decide
  let e := pairOrder 0 j
  have first : e 0 = 0 := pairOrder_first _ _ distinct
  have second : e 1 = j := pairOrder_second _ _ distinct
  have zero (a : Bool) : sliceSix h e true a = 0 := by
    funext x
    by_contra hn
    have member := (support (fillSix e a true x)).mp hn
    have same := (Finset.mem_filter.mp member).2.1
    have pair := fillSix_pair_parity e a true x
    rw [first,second] at pair
    change (fillSix e a true x) 0 = (fillSix e a true x) j at same
    rw [same,Bool.xor_self] at pair
    contradiction
  exact ⟨e,zero false,zero true⟩

/-- Exact all-C/C support case, once its actual four-flat coordinates have
been internally obtained: some literal sector must vanish. -/
theorem normalized_four_flat_has_zero_sector {m : ℕ} (h : Signature ℂ 6)
    (deck : OrderedRootDeck m h) (edge : Fin 6) (a b o : Bool)
    (support : ∀ w, h w ≠ 0 ↔ w ∈ flatSupport edge a b o) :
    ∃ e : Equiv.Perm (Fin 6), ZeroSector h e true := by
  have matching := normalized_atlas_forces_matching h deck edge a b o support
  rcases matching with ⟨rfl,rfl,rfl⟩
  have equality : flatSupport 0 false true o = nativeMatchingSupport o := by
    cases o <;> decide
  apply normalized_matching_zero_sector h o
  intro w
  simpa only [equality] using support w

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSixPort
