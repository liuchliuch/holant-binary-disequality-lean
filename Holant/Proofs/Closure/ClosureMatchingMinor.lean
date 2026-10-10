import Holant.Certificates.MatchingContractionClosure.NonzeroProducts
import Holant.Proofs.FiniteGroups.Stabilization.BinaryPrimes

/-! Intrinsic two-port minors recover the literal matching of a nonzero product
of nonsingular binaries, over the original field. A cross pair has every local
minor zero; every true edge has one nonzero local minor. No support-parity or
analytic unique-factorization oracle is assumed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureMatchingMinor
open Holant Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open scoped BigOperators
variable {K P E : Type*} [Field K] [DecidableEq P] [Fintype E] [DecidableEq E]

def minor (f : Tensor K P) (u v : P) (x : P → Bool) : K :=
  f (insertPair u v false false x) * f (insertPair u v true true x) -
    f (insertPair u v false true x) * f (insertPair u v true false x)

private theorem port_ne (p : (E × Bool) ≃ P) (e : E) (u : P)
    (h : (p.symm u).1 ≠ e) (b : Bool) : p (e,b) ≠ u := by
  intro he
  apply h
  rw [← he,Equiv.symm_apply_apply]

/-- Every original factor depends on at most one of the two crossed bits. -/
theorem cross_minor_zero (p : (E × Bool) ≃ P) (A : E → Binary (K:=K)) (c : K)
    (u v : P) (different : (p.symm u).1 ≠ (p.symm v).1) (x : P → Bool) :
    minor (productValue p A c) u v x = 0 := by
  classical
  let value := fun e a b =>
    A e (insertPair u v a b x (p (e,false))) (insertPair u v a b x (p (e,true)))
  have factor (e : E) : value e false false * value e true true =
      value e false true * value e true false := by
    by_cases hu : (p.symm u).1 = e
    · have hv : (p.symm v).1 ≠ e := fun h => different (hu.trans h.symm)
      have independent (a b : Bool) : value e a b = value e a false := by
        simp [value,insertPair,Function.update_apply,port_ne p e v hv false,port_ne p e v hv true]
      rw [independent true true,independent false true]
    · have independent (a b : Bool) : value e a b = value e false b := by
        simp [value,insertPair,Function.update_apply,port_ne p e u hu false,port_ne p e u hu true]
      rw [independent true true,independent true false]
      exact mul_comm _ _
  have products : (∏ e,value e false false) * (∏ e,value e true true) =
      (∏ e,value e false true) * (∏ e,value e true false) := by
    rw [← Finset.prod_mul_distrib,← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro e _
    exact factor e
  change (c * ∏ e,value e false false) * (c * ∏ e,value e true true) -
      (c * ∏ e,value e false true) * (c * ∏ e,value e true false) = 0
  calc
    _ = c^2 * ((∏ e,value e false false) * (∏ e,value e true true) -
      (∏ e,value e false true) * (∏ e,value e true false)) := by ring
    _ = 0 := by rw [products]; ring

/-- The true-edge local minor is its actual binary determinant times the
square of the untouched coefficient product. -/
theorem edge_minor (p : (E × Bool) ≃ P) (A : E → Binary (K:=K)) (c : K)
    (e : E) (x : P → Bool) :
    minor (productValue p A c) (p (e,false)) (p (e,true)) x =
      Matrix.det (A e) * (c * ∏ d ∈ {e}ᶜ, A d (x (p (d,false))) (x (p (d,true))))^2 := by
  simp only [minor,product_extract_edge,binary_det_formula]
  ring

theorem edge_minor_nonzero (p : (E × Bool) ≃ P) (A : E → Binary (K:=K)) (c : K)
    (nonzero : productValue p A c ≠ 0) (e : E) (nonsingular : Matrix.det (A e) ≠ 0) :
    ∃ x : P → Bool, minor (productValue p A c) (p (e,false)) (p (e,true)) x ≠ 0 := by
  classical
  have witness : ∃ x, productValue p A c x ≠ 0 := by
    by_contra hn
    apply nonzero
    funext x
    by_contra hx
    exact hn ⟨x,hx⟩
  obtain ⟨x,hx⟩ := witness
  have same : insertPair (p (e,false)) (p (e,true)) (x (p (e,false))) (x (p (e,true))) x = x := by
    simp [insertPair]
  have extract := product_extract_edge p A c e (x (p (e,false))) (x (p (e,true))) x
  rw [same] at extract
  rw [extract] at hx
  refine ⟨x,?_⟩
  rw [edge_minor]
  exact mul_ne_zero nonsingular (pow_ne_zero 2 (mul_ne_zero_iff.mp hx).2)

/-- Equal full tensors force every actual source edge to be a target edge.
Only the source factors' nonsingularity is required for this direction. -/
theorem edge_preserved {N : Type*} [Fintype N] [DecidableEq N]
    (p : (E × Bool) ≃ P) (A : E → Binary (K:=K)) (c : K)
    (q : (N × Bool) ≃ P) (B : N → Binary (K:=K)) (d : K)
    (nonzero : productValue p A c ≠ 0) (nonsingular : ∀ e, Matrix.det (A e) ≠ 0)
    (same : productValue p A c = productValue q B d) (e : E) :
    (q.symm (p (e,false))).1 = (q.symm (p (e,true))).1 := by
  by_contra different
  obtain ⟨x,hx⟩ := edge_minor_nonzero p A c nonzero e (nonsingular e)
  apply hx
  rw [same]
  exact cross_minor_zero q B d _ _ different x

/-- The mate is determined by the actual original port bijection. -/
def mate (p : (E × Bool) ≃ P) (u : P) : P := p ((p.symm u).1,!(p.symm u).2)

private theorem mate_of_same_edge (p : (E × Bool) ≃ P) (u v : P) (distinct : u ≠ v)
    (same : (p.symm u).1 = (p.symm v).1) : mate p u = v := by
  have different : (p.symm u).2 ≠ (p.symm v).2 := by
    intro he
    exact distinct (p.symm.injective (Prod.ext same he))
  have flip : Bool.not ((p.symm u).2) = (p.symm v).2 := by
    cases h₀ : (p.symm u).2 <;> cases h₁ : (p.symm v).2 <;> simp_all
  apply p.symm.injective
  simpa only [mate,Equiv.symm_apply_apply] using
    (show ((p.symm u).1, Bool.not ((p.symm u).2)) = p.symm v from Prod.ext same flip)

/-- No ambiguity of literal matching remains after changing factor scalars,
edge enumeration or orientation. This is derived from actual coefficient minors. -/
theorem mate_eq_of_tensor_eq {N : Type*} [Fintype N] [DecidableEq N]
    (p : (E × Bool) ≃ P) (A : E → Binary (K:=K)) (c : K)
    (q : (N × Bool) ≃ P) (B : N → Binary (K:=K)) (d : K)
    (nonzero : productValue p A c ≠ 0) (nonsingular : ∀ e, Matrix.det (A e) ≠ 0)
    (same : productValue p A c = productValue q B d) : mate p = mate q := by
  funext u
  obtain ⟨⟨e,b⟩,rfl⟩ := p.surjective u
  have pair := edge_preserved p A c q B d nonzero nonsingular same e
  have distinct : p (e,false) ≠ p (e,true) := by
    intro he
    have hb := congrArg Prod.snd (p.injective he)
    cases hb
  cases b
  · simpa only [mate,Equiv.symm_apply_apply,Bool.not_false] using
      (mate_of_same_edge q (p (e,false)) (p (e,true)) distinct pair).symm
  · simpa only [mate,Equiv.symm_apply_apply,Bool.not_true] using
      (mate_of_same_edge q (p (e,true)) (p (e,false)) distinct.symm pair.symm).symm

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureMatchingMinor
end
