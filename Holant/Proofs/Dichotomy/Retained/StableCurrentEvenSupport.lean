import Holant.Tractable.Conformal.MatrixSupport

/-! Exact product formula for a complementary support pair. The unary keeps
both original coefficients; the remaining factors only compare original ports.
This is a membership proof, not a claim that the individual factors are gadgets. -/
noncomputable section
set_option maxHeartbeats 1200000
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableCurrentEvenSupport
open Holant Holant.Tractable
open scoped BigOperators

def signedLink {n : ℕ} (s : Fin n → Bool) (i j : Fin n) : ProductFactor n :=
  if s i = s j then .equality i j else .disequality i j

theorem signedLink_eval {n : ℕ} (s x : Fin n → Bool) (i j : Fin n) :
    (signedLink s i j).eval x =
      if x j = (if x i = s i then s j else !(s j)) then 1 else 0 := by
  cases hi : s i <;> cases hj : s j <;> cases hxi : x i <;> cases hxj : x j <;>
    simp [signedLink,ProductFactor.eval,Signature.equality,Signature.disequality,hi,hj,hxi,hxj]

theorem product_finset {n : ℕ} {ι : Type*} (S : Finset ι)
    (f : ι → Signature AlgebraicComplex n) (each : ∀ i ∈ S, Product (f i)) :
    Product (fun x => ∏ i ∈ S, f i x) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using product_constant n 1
  | @insert i S absent ih =>
      have pi := each i (Finset.mem_insert_self i S)
      have ps := ih (fun j hj => each j (Finset.mem_insert_of_mem hj))
      simpa only [Finset.prod_insert absent] using pi.mul ps

/-- All arities, including zero endpoint coefficients. The only hypothesis is
the literal support constraint, not membership in any tractable class. -/
theorem product_of_complementary_support {n : ℕ} (f : Signature AlgebraicComplex n)
    (anchor : Fin n) (s : Fin n → Bool)
    (support : ∀ x, x ≠ s → x ≠ complementWord s → f x = 0) : Product f := by
  classical
  let links : Signature AlgebraicComplex n := fun x =>
    ∏ j : Fin n, (signedLink s anchor j).eval x
  have hlinks : Product links :=
    product_finset Finset.univ (fun j => (signedLink s anchor j).eval)
      (fun j _ => product_factor (signedLink s anchor j))
  let coefficient : Bool → AlgebraicComplex := fun b =>
    if b = s anchor then f s else f (complementWord s)
  have hproduct := (product_unary anchor coefficient).mul hlinks
  convert hproduct using 1
  funext x
  have chosen : links x = if x = (fun j => if x anchor = s anchor then s j else !(s j))
      then 1 else 0 := by
    dsimp only [links]
    simp_rw [signedLink_eval]
    by_cases he : x = (fun j => if x anchor = s anchor then s j else !(s j))
    · rw [ite_eq_left he]
      apply Finset.prod_eq_one
      intro j _
      exact ite_eq_left (congrFun he j)
    · have hn : ∃ j, x j ≠ (if x anchor = s anchor then s j else !(s j)) := by
        by_contra hn
        push Not at hn
        exact he (funext hn)
      obtain ⟨j,hj⟩ := hn
      rw [ite_eq_right he]
      exact Finset.prod_eq_zero (Finset.mem_univ j) (ite_eq_right hj)
  rw [chosen]
  by_cases same : x anchor = s anchor
  · simp only [same,ite_true,coefficient]
    by_cases word : x = s
    · simp [word]
    · have other : x ≠ complementWord s := by
        intro h
        have ha := congrFun h anchor
        rw [same] at ha
        cases hs : s anchor <;> simp [complementWord,hs] at ha
      simp [word,support x word other]
  · simp only [same,ite_false,coefficient]
    change f x = f (complementWord s) * (if x = complementWord s then 1 else 0)
    by_cases word : x = complementWord s
    · simp [word]
    · have other : x ≠ s := fun h => same (congrFun h anchor)
      simp [word,support x other word]

/-- Complement closure and at most two supported words force exactly one
complementary pair whenever the signature is nonzero. -/
theorem product_of_complement_closed_small {n : ℕ} (f : Signature AlgebraicComplex n)
    (anchor : Fin n) (closed : ∀ x, f (complementWord x) = 0 ↔ f x = 0)
    (small : ((Finset.univ : Finset (Fin n → Bool)).filter fun x => f x ≠ 0).card ≤ 2) :
    Product f := by
  classical
  by_cases zero : f = 0
  · exact Or.inl zero
  obtain ⟨s,hs⟩ : ∃ s, f s ≠ 0 := by
    by_contra none
    push Not at none
    exact zero (funext none)
  have hc : f (complementWord s) ≠ 0 := (closed s).not.mpr hs
  have distinct : s ≠ complementWord s := by
    intro he
    have h := congrFun he anchor
    cases hb : s anchor <;> simp [complementWord,hb] at h
  have pairSubset : ({s,complementWord s} : Finset (Fin n → Bool)) ⊆
      Finset.univ.filter (fun x => f x ≠ 0) := by
    intro x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> simp [hs,hc]
  have exactPair : ({s,complementWord s} : Finset (Fin n → Bool)) =
      Finset.univ.filter (fun x => f x ≠ 0) :=
    Finset.eq_of_subset_of_card_le pairSubset (by simpa [distinct] using small)
  apply product_of_complementary_support f anchor s
  intro x hxs hxc
  by_contra nonzero
  have hx : x ∈ ({s,complementWord s} : Finset (Fin n → Bool)) := by
    rw [exactPair]
    simp [nonzero]
  simp [hxs,hxc] at hx

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableCurrentEvenSupport
end
