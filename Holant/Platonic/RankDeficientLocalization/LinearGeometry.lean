import Holant.Certificates.PlatonicIncidence.ProjectiveDomainGraph
import Holant.Platonic.RainbowLocalization.ThreePoints
import Holant.Platonic.RainbowLocalization.SpanDimension

/-! Exact linear geometry behind kernel-deleted rainbow localization. -/
noncomputable section
namespace Holant.Platonic.RankDeficientLocalization
open Holant Holant.Certificates.MatchingProductBridge
open Holant.Certificates.PlatonicIncidence Holant.Certificates.RainbowOrbit
open Holant.Certificates.MatchingContractionClosure Holant.Platonic.RainbowLocalization
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The literal binary-matrix domain has dimension four. -/
theorem matrix_domain_finrank : Module.finrank ℂ Mat = 4 := by
  simp [Mat, Module.finrank_matrix]

theorem kernel_dimension_le_two (Φ : Mat →ₗ[ℂ] V)
    (hr : 2 ≤ Module.finrank ℂ Φ.range) : Module.finrank ℂ Φ.ker ≤ 2 := by
  have h := Φ.finrank_range_add_finrank_ker
  rw [matrix_domain_finrank] at h
  omega

theorem map_rank_le_four (Φ : Mat →ₗ[ℂ] V) : Module.finrank ℂ Φ.range ≤ 4 := by
  have h := Φ.finrank_range_add_finrank_ker
  rw [matrix_domain_finrank] at h
  omega

theorem images_independent (Φ : Mat →ₗ[ℂ] V) (u v : Mat)
    (hu : Φ u ≠ 0) (hv : Φ v ≠ 0) (hn : ¬ Proportional (Φ u) (Φ v)) :
    LinearIndependent ℂ ![Φ u,Φ v] := by
  apply linearIndependent_fin2.mpr
  refine ⟨hv,?_⟩
  intro c hc
  apply hn
  refine ⟨c,?_,hc.symm⟩
  intro hz
  exact hu (by simpa [hz] using hc.symm)

/-- Two nonproportional images force injectivity on their entire source line,
not just on the surviving configuration points. -/
theorem span_pair_disjoint_kernel (Φ : Mat →ₗ[ℂ] V) (u v : Mat)
    (hu : Φ u ≠ 0) (hv : Φ v ≠ 0) (hn : ¬ Proportional (Φ u) (Φ v)) :
    Disjoint (Submodule.span ℂ ({u,v} : Set Mat)) Φ.ker := by
  have hli : LinearIndependent ℂ (Φ ∘ (![u,v] : Fin 2 → Mat)) := by
    have he : Φ ∘ (![u,v] : Fin 2 → Mat) = ![Φ u,Φ v] := by
      funext i; fin_cases i <;> rfl
    rw [he]
    exact images_independent Φ u v hu hv hn
  simpa only [Matrix.range_cons_cons_empty] using Submodule.range_ker_disjoint hli

theorem span_pair_injOn (Φ : Mat →ₗ[ℂ] V) (u v : Mat)
    (hu : Φ u ≠ 0) (hv : Φ v ≠ 0) (hn : ¬ Proportional (Φ u) (Φ v)) :
    Set.InjOn Φ (Submodule.span ℂ ({u,v} : Set Mat)) :=
  LinearMap.injOn_of_disjoint_ker le_rfl (span_pair_disjoint_kernel Φ u v hu hv hn)

theorem matrix_subspace_eq_pair {n : ℕ} (U : Fin n → Mat) (hU : ∀i,U i ≠ 0)
    (hf : ∀i j (c : ℂ),U i=c • U j → i=j) (L : Submodule ℂ Mat)
    (hL : Module.finrank ℂ L ≤ 2) (i j : Fin n) (hne : i≠j)
    (hi : U i∈L) (hj : U j∈L) :
    L=Submodule.span ℂ ({U i,U j} : Set Mat) := by
  have hle : Submodule.span ℂ ({U i,U j} : Set Mat) ≤ L := by
    apply Submodule.span_le.mpr
    intro z hz
    rcases hz with rfl|rfl <;> assumption
  exact (Submodule.eq_of_le_of_finrank_le hle
    (by rw [matrix_pair_dimension U hU hf i j hne]; exact hL)).symm

/-- Actual graph edges can be rebased at their endpoints. -/
theorem matrix_adj_rich_pair {n : ℕ} (U : Fin n → Mat) (hU : ∀i,U i≠0)
    (hf : ∀i j (c : ℂ),U i=c • U j → i=j) (i j : Fin n)
    (ha : (matrixGraph U).Adj i j) :
    3 ≤ (matrixIntersection U (Submodule.span ℂ ({U i,U j} : Set Mat))).card := by
  obtain ⟨hne,S,⟨a,b,hab,hS⟩,hc,hi,hj⟩ := ha
  let L := Submodule.span ℂ ({U a,U b} : Set Mat)
  have hL : L=Submodule.span ℂ ({U i,U j} : Set Mat) :=
    matrix_subspace_eq_pair U hU hf L (le_of_eq (matrix_pair_dimension U hU hf a b hab))
      i j hne ((hS i).mp hi) ((hS j).mp hj)
  have he : matrixIntersection U L=S := Finset.ext (fun k => (mem_matrixIntersection U L k).trans (hS k).symm)
  rw [←hL,he]
  exact hc

/-- Connectivity produces a matching-changing edge; the labels here will be
chosen from literal nonzero card presentations by the source theorem. -/
theorem connected_exists_changed_edge {I C : Type*} (G : SimpleGraph I)
    (hc : G.Connected) (c : I → C) (i j : I) (hne : c i≠c j) :
    ∃a b,G.Adj a b ∧ c a≠c b := by
  classical
  by_contra hn
  push_neg at hn
  obtain ⟨w⟩ := hc i j
  have he : c i=c j := by
    clear hne
    induction w with
    | nil => rfl
    | @cons a b z hab w ih => exact (hn a b hab).trans ih
  exact hne he

theorem rank_ge_two_of_nonproportional {W : Type*} [AddCommGroup W] [Module ℂ W]
    [Module.Finite ℂ W] (Φ : W →ₗ[ℂ] V) (u v : W)
    (hu : Φ u≠0) (hv : Φ v≠0) (hn : ¬Proportional (Φ u) (Φ v)) :
    2≤Module.finrank ℂ Φ.range := by
  have hle : Submodule.span ℂ ({Φ u,Φ v} : Set V)≤Φ.range := by
    apply Submodule.span_le.mpr
    intro z hz
    rcases hz with rfl|rfl
    · exact ⟨u,rfl⟩
    · exact ⟨v,rfl⟩
  have h := Submodule.finrank_mono hle
  rwa [nonproportional_span_pair_finrank _ _ hu hv hn] at h

end Holant.Platonic.RankDeficientLocalization
