import Holant.ReedMuller.FlatNetwork.GenerationNetworkBasic

/-! Literal I/RM networks have only zero-one summands. Consequently exact
scalar-one realization supplies exactly one internal lift of every supported
boundary word, rather than obtaining one through cancellation. -/
namespace Holant.ReedMuller.FlatNetwork
open Holant Holant.ReedMuller.LowArity
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace GenerationNetwork
variable {n : ℕ}

def ValidLift (N : Network ℂ n) (x : Fin n → Bool)
    (z : (Fin N.shape.edges × Bool) → Bool) : Prop :=
  (∀ v, N.vertex v (N.shape.assignment x z v) = 1) ∧
    ∀ e, N.edge e (z (e,false)) (z (e,true)) = 1

private def ZeroOneSignature (f : AnySignature ℂ) : Prop :=
  ∀ x, f.2 x = 0 ∨ f.2 x = 1

theorem allowed_vertex_zero_one (N : Network ℂ n) (hN : Allowed N)
    (v : Fin N.shape.vertices) (x : Fin (N.shape.arity v) → Bool) :
    N.vertex v x = 0 ∨ N.vertex v x = 1 := by
  have hz : ZeroOneSignature ⟨N.shape.arity v,N.vertex v⟩ := by
    rcases hN.1 v with hi | hr
    · rw [hi]
      intro x
      dsimp
      unfold Signature.equality
      split_ifs <;> simp
    · rw [hr]
      intro x
      dsimp
      rw [rmCore, flat_zero_value]
      split_ifs <;> simp
  exact hz x

theorem allowed_edge_zero_one (N : Network ℂ n) (hN : Allowed N)
    (e : Fin N.shape.edges) (a b : Bool) : N.edge e a b = 0 ∨ N.edge e a b = 1 := by
  rcases hN.2 e with hi | hx
  · rw [hi]
    unfold Signature.equality
    split_ifs <;> simp
  · rw [hx]
    unfold Signature.disequality
    split_ifs <;> simp

private theorem prod_zero_one {ι : Type*} [Fintype ι] (f : ι → ℂ)
    (hf : ∀ i, f i = 0 ∨ f i = 1) :
    ∏ i, f i = if ∀ i, f i = 1 then 1 else 0 := by
  by_cases h : ∀ i, f i = 1
  · simp [h]
  · rw [if_neg h]
    obtain ⟨i, hi⟩ := not_forall.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) ((hf i).resolve_right hi)

theorem denote_eq_lift_count (N : Network ℂ n) (hN : Allowed N) (x : Fin n → Bool) :
    N.denote x = ((Finset.univ.filter (ValidLift N x)).card : ℂ) := by
  unfold Network.denote
  have hv (z : (Fin N.shape.edges × Bool) → Bool) :
      (∏ v, N.vertex v (N.shape.assignment x z v)) =
      if ∀ v, N.vertex v (N.shape.assignment x z v) = 1 then 1 else 0 :=
    (prod_zero_one (fun v => N.vertex v (N.shape.assignment x z v))
      (fun v => allowed_vertex_zero_one N hN v (N.shape.assignment x z v))).trans (by split_ifs <;> rfl)
  have he (z : (Fin N.shape.edges × Bool) → Bool) :
      (∏ e, N.edge e (z (e,false)) (z (e,true))) =
      if ∀ e, N.edge e (z (e,false)) (z (e,true)) = 1 then 1 else 0 :=
    (prod_zero_one (fun e => N.edge e (z (e,false)) (z (e,true)))
      (fun e => allowed_edge_zero_one N hN e (z (e,false)) (z (e,true)))).trans (by split_ifs <;> rfl)
  simp only [hv, he]
  rw [← Finset.sum_boole]
  apply Finset.sum_congr rfl
  intro z _
  unfold ValidLift
  split_ifs <;> simp_all

/-- Scalar one has a unique literal internal endpoint assignment. -/
theorem unique_lift_of_denote_one (N : Network ℂ n) (hN : Allowed N) (x : Fin n → Bool)
    (hx : N.denote x = 1) : ∃! z, ValidLift N x z := by
  rw [denote_eq_lift_count N hN x] at hx
  have hc : (Finset.univ.filter (ValidLift N x)).card = 1 := by exact_mod_cast hx
  obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hc
  have hm : z ∈ Finset.univ.filter (ValidLift N x) := by rw [hz]; simp
  refine ⟨z, (Finset.mem_filter.mp hm).2, ?_⟩
  intro y hy
  have hm' : y ∈ Finset.univ.filter (ValidLift N x) := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hy⟩
  rw [hz] at hm'
  exact Finset.mem_singleton.mp hm'

end GenerationNetwork
end
end Holant.ReedMuller.FlatNetwork
